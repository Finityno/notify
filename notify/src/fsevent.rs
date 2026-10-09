//! Watcher implementation for Darwin's FSEvents API
//!
//! The FSEvents API provides a mechanism to notify clients about directories they ought to re-scan
//! in order to keep their internal data structures up-to-date with respect to the true state of
//! the file system. (For example, when files or directories are created, modified, or removed.) It
//! sends these notifications "in bulk", possibly notifying the client of changes to several
//! directories in a single callback.
//!
//! For more information see the [FSEvents API reference][ref].
//!
//! TODO: document event translation
//!
//! [ref]: https://developer.apple.com/library/mac/documentation/Darwin/Reference/FSEvents_Ref/

#![allow(non_upper_case_globals, dead_code)]

use crate::paths::{absolute_path, reported_path};
use crate::{
    Config, Error, ErrorKind, EventHandler, EventKindMask, RecursiveMode, Result, Sender, Watcher,
    unbounded,
};
use crate::{PathOp, event::*};
use objc2_core_foundation as cf;
use objc2_core_services as fs;
use std::collections::{HashMap, HashSet};
use std::ffi::{CStr, OsStr};
use std::fmt;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::ptr::{self, NonNull};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

bitflags::bitflags! {
  #[repr(C)]
  #[derive(Debug)]
  struct StreamFlags: u32 {
    const NONE = fs::kFSEventStreamEventFlagNone;
    const MUST_SCAN_SUBDIRS = fs::kFSEventStreamEventFlagMustScanSubDirs;
    const USER_DROPPED = fs::kFSEventStreamEventFlagUserDropped;
    const KERNEL_DROPPED = fs::kFSEventStreamEventFlagKernelDropped;
    const IDS_WRAPPED = fs::kFSEventStreamEventFlagEventIdsWrapped;
    const HISTORY_DONE = fs::kFSEventStreamEventFlagHistoryDone;
    const ROOT_CHANGED = fs::kFSEventStreamEventFlagRootChanged;
    const MOUNT = fs::kFSEventStreamEventFlagMount;
    const UNMOUNT = fs::kFSEventStreamEventFlagUnmount;
    const ITEM_CREATED = fs::kFSEventStreamEventFlagItemCreated;
    const ITEM_REMOVED = fs::kFSEventStreamEventFlagItemRemoved;
    const INODE_META_MOD = fs::kFSEventStreamEventFlagItemInodeMetaMod;
    const ITEM_RENAMED = fs::kFSEventStreamEventFlagItemRenamed;
    const ITEM_MODIFIED = fs::kFSEventStreamEventFlagItemModified;
    const FINDER_INFO_MOD = fs::kFSEventStreamEventFlagItemFinderInfoMod;
    const ITEM_CHANGE_OWNER = fs::kFSEventStreamEventFlagItemChangeOwner;
    const ITEM_XATTR_MOD = fs::kFSEventStreamEventFlagItemXattrMod;
    const IS_FILE = fs::kFSEventStreamEventFlagItemIsFile;
    const IS_DIR = fs::kFSEventStreamEventFlagItemIsDir;
    const IS_SYMLINK = fs::kFSEventStreamEventFlagItemIsSymlink;
    const OWN_EVENT = fs::kFSEventStreamEventFlagOwnEvent;
    const IS_HARDLINK = fs::kFSEventStreamEventFlagItemIsHardlink;
    const IS_LAST_HARDLINK = fs::kFSEventStreamEventFlagItemIsLastHardlink;
    const ITEM_CLONED = fs::kFSEventStreamEventFlagItemCloned;
  }
}

/// FSEvents-based `Watcher` implementation
pub struct FsEventWatcher {
    since_when: fs::FSEventStreamEventId,
    latency: cf::CFTimeInterval,
    flags: fs::FSEventStreamCreateFlags,
    event_handler: Arc<Mutex<dyn EventHandler>>,
    runloop: Option<RunLoopHandle>,
    watches: HashMap<PathBuf, WatchEntry>,
    event_kinds: EventKindMask,
    swap_mechanism: SwapMechanism,
    // Devices fseventsd keeps an event history for, which a replay needs.
    devices_with_history: HashSet<u64>,
    // Shared with every stream's callback; see `RootIdentity`.
    root_identities: Arc<Mutex<HashMap<PathBuf, RootIdentity>>>,
}

// `cf_path` is kept out of `WatchInfo` because `WatchInfo` is cloned into the stream
// context, which must stay `Send + Sync`.
#[derive(Debug)]
struct WatchEntry {
    info: WatchInfo,
    cf_path: cf::CFRetained<cf::CFString>,
    device: u64,
}

#[derive(Clone, Debug)]
struct WatchInfo {
    is_recursive: bool,
    reported_path: PathBuf,
}

// FSEvents applies the path limit across live streams, so all watcher instances
// in this process must share the same count.
static ACTIVE_FSEVENTS_PATHS: AtomicUsize = AtomicUsize::new(0);

#[derive(Debug)]
struct FseventsPathReservation {
    active_paths: &'static AtomicUsize,
    path_count: usize,
}

impl FseventsPathReservation {
    fn acquire(
        active_paths: &'static AtomicUsize,
        path_count: usize,
        budget: usize,
    ) -> std::result::Result<Self, usize> {
        active_paths
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |active_path_count| {
                active_path_count
                    .checked_add(path_count)
                    .filter(|&combined_path_count| combined_path_count <= budget)
            })
            .map(|_| Self {
                active_paths,
                path_count,
            })
    }
}

impl Drop for FseventsPathReservation {
    fn drop(&mut self) {
        let previous = self
            .active_paths
            .fetch_sub(self.path_count, Ordering::Relaxed);
        debug_assert!(previous >= self.path_count);
    }
}

#[derive(Debug)]
struct RunLoopHandle {
    runloop: cf::CFRetained<cf::CFRunLoop>,
    stop_source: cf::CFRetained<cf::CFRunLoopSource>,
    flush_source: cf::CFRetained<cf::CFRunLoopSource>,
    thread_handle: thread::JoinHandle<()>,
    progress: Arc<StreamProgress>,
    recursive_info: Arc<HashMap<PathBuf, WatchInfo>>,
    // The paths the stream was created with, when it watches them with
    // `kFSEventStreamCreateFlagWatchRoot`.
    watched_roots: Vec<PathBuf>,
    stream_number: u64,
}

// How a swap keeps the events the old stream has not delivered yet. The
// single-mechanism variants exist so the Mac tests can show which mechanism
// actually delivers a held event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SwapMechanism {
    FlushAndReplay,
    FlushOnly,
    ReplayOnly,
}

impl SwapMechanism {
    fn flushes(self) -> bool {
        matches!(self, Self::FlushAndReplay | Self::FlushOnly)
    }

    fn replays(self) -> bool {
        matches!(self, Self::FlushAndReplay | Self::ReplayOnly)
    }
}

// Flush requests from `restart`, the flush source's answers to them, and what
// the stream's callback has handed to the event handler; `restart` waits on it
// before stopping the stream, and reads it to decide where the replacement
// stream resumes.
#[derive(Debug)]
struct StreamProgress {
    state: Mutex<FlushState>,
    changed: Condvar,
}

impl StreamProgress {
    fn new(start_event_id: fs::FSEventStreamEventId, history_pending: bool) -> Self {
        Self {
            state: Mutex::new(FlushState::new(start_event_id, history_pending)),
            changed: Condvar::new(),
        }
    }
}

// A flush is complete once the flush source has answered it and the callback
// has handed the event handler every event the service had queued for the
// stream when it was asked. That is decided by the ids the callback has seen,
// not by `FSEventStreamFlushSync` returning. A held zero-id `RootChanged`
// event alone cannot be waited for this way. The generation keeps a flush
// answered before a request was made from satisfying it.
//
// On macOS 27 the flush alone did not deliver an event held for the latency:
// the wait ended within 5 ms and the event never arrived, so the id the flush
// returned was already delivered. The replacement stream therefore also
// replays history from `delivered`; see `replay_since`.
#[derive(Debug)]
struct FlushState {
    requested: u64,
    answered: u64,
    flush_target: fs::FSEventStreamEventId,
    // The highest event id the callback has seen, or, before the first
    // callback, the id the stream started from. Every event the stream still
    // owes has a larger id.
    delivered: fs::FSEventStreamEventId,
    started_at: Instant,
    last_delivery_at: Option<Instant>,
    // Started from a historical id and the `HistoryDone` sentinel has not
    // arrived, so older events may be owed however long ago the last callback
    // ran.
    history_pending: bool,
    retiring: bool,
}

impl FlushState {
    fn new(start_event_id: fs::FSEventStreamEventId, history_pending: bool) -> Self {
        Self {
            requested: 0,
            answered: 0,
            flush_target: 0,
            delivered: start_event_id,
            started_at: Instant::now(),
            last_delivery_at: None,
            history_pending,
            retiring: false,
        }
    }

    fn request(&mut self) -> u64 {
        self.requested += 1;
        self.requested
    }

    // Taken before the flush starts, so a request made while it runs is not
    // reported answered by it.
    fn pending(&self) -> u64 {
        self.requested
    }

    // `queued` is what `FSEventStreamFlushAsync` returned: the largest id ever
    // queued for the stream, or 0 if none was.
    fn answer(&mut self, generation: u64, queued: fs::FSEventStreamEventId) {
        self.answered = self.answered.max(generation);
        self.flush_target = self.flush_target.max(queued);
    }

    fn record_delivery(&mut self, highest_id: fs::FSEventStreamEventId, now: Instant) {
        self.delivered = self.delivered.max(highest_id);
        self.last_delivery_at = Some(now);
    }

    fn is_complete(&self, generation: u64) -> bool {
        self.answered >= generation && self.delivered >= self.flush_target
    }

    // With `NoDefer`, an event is held only while a delivery happened within
    // the latency; after a quiet period the next one is delivered at once. A
    // young stream counts as active because events can be on their way to it
    // from before its first callback.
    fn may_hold_events(&self, now: Instant, hold_window: Duration) -> bool {
        let last_activity = self
            .last_delivery_at
            .map_or(self.started_at, |delivered_at| {
                delivered_at.max(self.started_at)
            });
        self.history_pending || now.saturating_duration_since(last_activity) <= hold_window
    }
}

// Bounds how long a swap waits for the old stream's flushed events to pass
// through the event handler. Hitting it means the handler or fseventsd is
// wedged; the swap then goes ahead without the guarantee rather than hanging the
// watch call.
const FLUSH_TIMEOUT: Duration = Duration::from_secs(5);

// Slack on top of the latency for a delivery the service has sent but the
// stream's runloop has not run yet.
const REPLAY_GRACE: Duration = Duration::from_secs(1);

// How far back, in system-wide event ids, a swap replays when the old stream
// is idle. Nothing is held then, but an event can still be on its way from
// fseventsd; it is among the most recent ids. The cap keeps a swap on a
// long-quiet watcher from reading the volume's history since its last event.
const IDLE_REPLAY_EVENTS: fs::FSEventStreamEventId = 10_000;

// Where the replacement stream resumes so that nothing the old stream still
// owes is lost: everything after the last id the old stream delivered while
// it may hold events, and otherwise only the most recent stretch of history.
// `None` means history cannot be used and the stream starts from now.
fn replay_since(
    delivered: fs::FSEventStreamEventId,
    current: fs::FSEventStreamEventId,
    may_hold_events: bool,
) -> Option<fs::FSEventStreamEventId> {
    let since_when = if may_hold_events {
        delivered
    } else {
        delivered.max(current.saturating_sub(IDLE_REPLAY_EVENTS))
    }
    .min(current);
    // 0 would replay the volume's whole history.
    (since_when != 0 && current != fs::kFSEventStreamEventIdSinceNow).then_some(since_when)
}

// What a stream started from a historical id must not deliver: events from
// before the watch call on paths the previous stream did not watch, and events
// the previous stream already delivered.
#[derive(Debug)]
struct ReplayFilter {
    since_when: fs::FSEventStreamEventId,
    // The current event id when the watch call began, sampled before the watch
    // set changed: an event on a newly watched path with a larger id happened
    // after the call started and is never classified `PredatesWatch`.
    swap_event_id: fs::FSEventStreamEventId,
    previous_watches: Arc<HashMap<PathBuf, WatchInfo>>,
    previous_progress: Arc<StreamProgress>,
    previous_stream: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ReplaySkip {
    PredatesWatch,
    AlreadyDelivered,
}

impl ReplayFilter {
    // `previous_delivered` is read once per batch: a stale value can only let
    // a duplicate through, never drop an event.
    fn skip(
        &self,
        path: &Path,
        event_id: fs::FSEventStreamEventId,
        previous_delivered: fs::FSEventStreamEventId,
    ) -> Option<ReplaySkip> {
        // Zero-id events such as `RootChanged` are made by the stream itself
        // and never come from history.
        if event_id == 0 || (event_id > self.swap_event_id && event_id > previous_delivered) {
            return None;
        }
        if find_watch(path, &self.previous_watches).is_some() {
            (event_id <= previous_delivered).then_some(ReplaySkip::AlreadyDelivered)
        } else {
            (event_id <= self.swap_event_id).then_some(ReplaySkip::PredatesWatch)
        }
    }
}

// A watched root's identity at the last moment the event handler was, or was
// about to be, told about every change to it before then: when the watch was
// added, just before a `RootChanged` event for it was handed over, or at a
// swap. A `RootChanged` event has id 0, so neither the flush, which waits for
// ids, nor the replay, which reads history, recovers one the old stream still
// held when it was stopped. A swap therefore compares each root the old stream
// watched against the identity recorded here and reports the ones that moved;
// the comparison does not depend on how long fseventsd holds the event. A
// reported change can repeat one the old stream delivered during the swap,
// which is acceptable; a missed one is not. A root renamed away and back
// between two checks keeps its identity and is not reported.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RootIdentity {
    Present { device: u64, inode: u64 },
    Missing,
}

impl RootIdentity {
    // `symlink_metadata`, because a watched root is a canonical path: a symlink
    // now standing there is a change, not the thing it points to.
    fn of(path: &Path) -> Self {
        std::fs::symlink_metadata(path).map_or(Self::Missing, |metadata| Self::from(&metadata))
    }
}

impl From<&std::fs::Metadata> for RootIdentity {
    fn from(metadata: &std::fs::Metadata) -> Self {
        Self::Present {
            device: metadata.dev(),
            inode: metadata.ino(),
        }
    }
}

// The roots among `previous_roots` that are still watched and whose identity
// differs from the recorded one, which is then brought up to date so the same
// change is reported once.
fn take_unreported_root_changes<'a>(
    previous_roots: &'a [PathBuf],
    recorded_identities: &mut HashMap<PathBuf, RootIdentity>,
    mut current_identity: impl FnMut(&Path) -> RootIdentity,
) -> Vec<&'a PathBuf> {
    previous_roots
        .iter()
        .filter(|root| {
            let Some(recorded) = recorded_identities.get_mut(root.as_path()) else {
                return false;
            };
            let current = current_identity(root);
            let changed = current != *recorded;
            *recorded = current;
            changed
        })
        .collect()
}

// The stat is taken under the lock, so it is ordered against a swap's
// comparison of the same root.
fn record_root_identity(root: &Path, identities: &Mutex<HashMap<PathBuf, RootIdentity>>) {
    let mut identities = lock_ignoring_poison(identities);
    if let Some(identity) = identities.get_mut(root) {
        *identity = RootIdentity::of(root);
    }
}

static NEXT_STREAM_NUMBER: AtomicU64 = AtomicU64::new(1);

fn debug_logging_enabled() -> bool {
    log::log_enabled!(log::Level::Debug) || debug_to_stderr()
}

#[cfg(test)]
fn debug_to_stderr() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED
        .get_or_init(|| std::env::var_os("NOTIFY_FSEVENT_DEBUG").is_some_and(|value| value == "1"))
}

#[cfg(not(test))]
fn debug_to_stderr() -> bool {
    false
}

#[cfg(test)]
fn debug_clock() -> Duration {
    static START: std::sync::OnceLock<Instant> = std::sync::OnceLock::new();
    START.get_or_init(Instant::now).elapsed()
}

macro_rules! fsevent_debug {
    ($($argument:tt)*) => {{
        log::debug!($($argument)*);
        #[cfg(test)]
        if debug_to_stderr() {
            eprintln!(
                "[fsevent {:>9.3}s {:?}] {}",
                debug_clock().as_secs_f64(),
                thread::current().id(),
                format_args!($($argument)*)
            );
        }
    }};
}

fn lock_ignoring_poison<T: ?Sized>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

impl fmt::Debug for FsEventWatcher {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("FsEventWatcher")
            .field("since_when", &self.since_when)
            .field("latency", &self.latency)
            .field("flags", &self.flags)
            .field("event_handler", &Arc::as_ptr(&self.event_handler))
            .field("runloop", &self.runloop)
            .field("watches", &self.watches)
            .field("swap_mechanism", &self.swap_mechanism)
            .finish()
    }
}

// FsEventWatcher is not Send/Sync automatically.
// It's Send because the pointer is not used in other threads.
unsafe impl Send for FsEventWatcher {}

// It's Sync because all methods that change the mutable state use `&mut self`.
unsafe impl Sync for FsEventWatcher {}

fn translate_flags(flags: StreamFlags, precise: bool) -> Vec<Event> {
    let mut evs = Vec::new();
    translate_flags_with(flags, precise, |ev| evs.push(ev));
    evs
}

// Keep this in sync with `translate_flags_with`; the callback uses it to avoid path clones.
fn translated_event_count(flags: &StreamFlags, precise: bool) -> usize {
    if flags.contains(StreamFlags::HISTORY_DONE) {
        return 0;
    }

    let mut count = usize::from(flags.contains(StreamFlags::MUST_SCAN_SUBDIRS));
    if !precise {
        return count + 1;
    }

    let root_changed = flags.contains(StreamFlags::ROOT_CHANGED);
    count += usize::from(root_changed);
    count += usize::from(flags.contains(StreamFlags::MOUNT));
    count += usize::from(flags.contains(StreamFlags::UNMOUNT));
    count += usize::from(flags.contains(StreamFlags::ITEM_CREATED));
    count += usize::from(flags.contains(StreamFlags::ITEM_RENAMED) && !root_changed);
    count += usize::from(flags.contains(StreamFlags::INODE_META_MOD));
    count += usize::from(flags.contains(StreamFlags::FINDER_INFO_MOD));
    count += usize::from(flags.contains(StreamFlags::ITEM_CHANGE_OWNER));
    count += usize::from(flags.contains(StreamFlags::ITEM_XATTR_MOD));
    count += usize::from(flags.contains(StreamFlags::ITEM_MODIFIED));
    count += usize::from(flags.contains(StreamFlags::ITEM_REMOVED) && !root_changed);
    count
}

fn translate_flags_with(flags: StreamFlags, precise: bool, mut emit: impl FnMut(Event)) {
    // «Denotes a sentinel event sent to mark the end of the "historical" events
    // sent as a result of specifying a `sinceWhen` value in the FSEvents.Create
    // call that created this event stream. After invoking the client's callback
    // with all the "historical" events that occurred before now, the client's
    // callback will be invoked with an event where the HistoryDone flag is set.
    // The client should ignore the path supplied in this callback.»
    // — https://www.mbsplugins.eu/FSEventsNextEvent.shtml
    //
    // As a result, we just stop processing here and return an empty vec, which
    // will ignore this completely and not emit any Events whatsoever.
    if flags.contains(StreamFlags::HISTORY_DONE) {
        return;
    }

    // `ITEM_CLONED` can be present alongside other flags (including create/modify/remove).
    // Preserve any existing `info` (like "root changed"), but annotate otherwise so downstream
    // can detect and filter clone-related events. See https://github.com/notify-rs/notify/issues/465.
    let clone_related = precise && flags.contains(StreamFlags::ITEM_CLONED);
    let own_process_id = if precise && flags.contains(StreamFlags::OWN_EVENT) {
        Some(std::process::id())
    } else {
        None
    };

    let mut emit_event = |mut ev: Event| {
        if clone_related && ev.info().is_none() {
            ev.attrs.set_info("is: clone");
        }
        if let Some(process_id) = own_process_id {
            ev.attrs.set_process_id(process_id);
        }
        emit(ev);
    };

    // FSEvents provides two possible hints as to why events were dropped,
    // however documentation on what those mean is scant, so we just pass them
    // through in the info attr field. The intent is clear enough, and the
    // additional information is provided if the user wants it.
    if flags.contains(StreamFlags::MUST_SCAN_SUBDIRS) {
        let e = Event::new(EventKind::Other).set_flag(Flag::Rescan);
        emit_event(if flags.contains(StreamFlags::USER_DROPPED) {
            e.set_info("rescan: user dropped")
        } else if flags.contains(StreamFlags::KERNEL_DROPPED) {
            e.set_info("rescan: kernel dropped")
        } else {
            e
        });
    }

    // In imprecise mode, let's not even bother parsing the kind of the event
    // except for the above very special events.
    if !precise {
        emit(Event::new(EventKind::Any));
        return;
    }

    // A watched root changed (renamed or removed). If the flags provide a hint,
    // prefer that over guessing. Otherwise, treat it as a removal to avoid
    // misclassifying a delete as a rename.
    let root_changed = flags.contains(StreamFlags::ROOT_CHANGED);
    if root_changed {
        let kind = if flags.contains(StreamFlags::ITEM_REMOVED) {
            if flags.contains(StreamFlags::IS_DIR) {
                EventKind::Remove(RemoveKind::Folder)
            } else if flags.contains(StreamFlags::IS_FILE) {
                EventKind::Remove(RemoveKind::File)
            } else {
                EventKind::Remove(RemoveKind::Any)
            }
        } else if flags.contains(StreamFlags::ITEM_RENAMED) {
            EventKind::Modify(ModifyKind::Name(RenameMode::From))
        } else {
            EventKind::Remove(RemoveKind::Any)
        };

        emit_event(Event::new(kind).set_info("root changed"));
    }

    // A path was mounted at the event path; we treat that as a create.
    if flags.contains(StreamFlags::MOUNT) {
        emit_event(Event::new(EventKind::Create(CreateKind::Other)).set_info("mount"));
    }

    // A path was unmounted at the event path; we treat that as a remove.
    if flags.contains(StreamFlags::UNMOUNT) {
        emit_event(Event::new(EventKind::Remove(RemoveKind::Other)).set_info("mount"));
    }

    if flags.contains(StreamFlags::ITEM_CREATED) {
        emit_event(if flags.contains(StreamFlags::IS_DIR) {
            Event::new(EventKind::Create(CreateKind::Folder))
        } else if flags.contains(StreamFlags::IS_FILE) {
            Event::new(EventKind::Create(CreateKind::File))
        } else {
            let e = Event::new(EventKind::Create(CreateKind::Other));
            if flags.contains(StreamFlags::IS_SYMLINK) {
                e.set_info("is: symlink")
            } else if flags.contains(StreamFlags::IS_HARDLINK) {
                e.set_info("is: hardlink")
            } else if flags.contains(StreamFlags::ITEM_CLONED) {
                e.set_info("is: clone")
            } else {
                Event::new(EventKind::Create(CreateKind::Any))
            }
        });
    }

    // FSEvents provides no mechanism to associate the old and new sides of a
    // rename event.
    // Avoid emitting duplicate events around a root change by checking `root_changed`.
    if flags.contains(StreamFlags::ITEM_RENAMED) && !root_changed {
        emit_event(Event::new(EventKind::Modify(ModifyKind::Name(
            RenameMode::Any,
        ))));
    }

    // This is only described as "metadata changed", but it may be that it's
    // only emitted for some more precise subset of events... if so, will need
    // amending, but for now we have an Any-shaped bucket to put it in.
    if flags.contains(StreamFlags::INODE_META_MOD) {
        emit_event(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Any,
        ))));
    }

    if flags.contains(StreamFlags::FINDER_INFO_MOD) {
        emit_event(
            Event::new(EventKind::Modify(ModifyKind::Metadata(MetadataKind::Other)))
                .set_info("meta: finder info"),
        );
    }

    if flags.contains(StreamFlags::ITEM_CHANGE_OWNER) {
        emit_event(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Ownership,
        ))));
    }

    if flags.contains(StreamFlags::ITEM_XATTR_MOD) {
        emit_event(Event::new(EventKind::Modify(ModifyKind::Metadata(
            MetadataKind::Extended,
        ))));
    }

    // This is specifically described as a data change, which we take to mean
    // is a content change.
    if flags.contains(StreamFlags::ITEM_MODIFIED) {
        emit_event(Event::new(EventKind::Modify(ModifyKind::Data(
            DataChange::Content,
        ))));
    }

    // Avoid emitting duplicate events around a root change by checking `root_changed`.
    if flags.contains(StreamFlags::ITEM_REMOVED) && !root_changed {
        emit_event(if flags.contains(StreamFlags::IS_DIR) {
            Event::new(EventKind::Remove(RemoveKind::Folder))
        } else if flags.contains(StreamFlags::IS_FILE) {
            Event::new(EventKind::Remove(RemoveKind::File))
        } else {
            let e = Event::new(EventKind::Remove(RemoveKind::Other));
            if flags.contains(StreamFlags::IS_SYMLINK) {
                e.set_info("is: symlink")
            } else if flags.contains(StreamFlags::IS_HARDLINK) {
                e.set_info("is: hardlink")
            } else if flags.contains(StreamFlags::ITEM_CLONED) {
                e.set_info("is: clone")
            } else {
                Event::new(EventKind::Remove(RemoveKind::Any))
            }
        });
    }
}

struct StreamContextInfo {
    event_handler: Arc<Mutex<dyn EventHandler>>,
    recursive_info: Arc<HashMap<PathBuf, WatchInfo>>,
    event_kinds: EventKindMask,
    progress: Arc<StreamProgress>,
    // Dropped at `HistoryDone`, so the previous stream's watch table is not
    // kept for the life of this stream. Without it, later events can only be
    // duplicates of the old stream's, never lost.
    replay: Mutex<Option<ReplayFilter>>,
    root_identities: Arc<Mutex<HashMap<PathBuf, RootIdentity>>>,
    stream_number: u64,
}

// Free the context when the stream created by `FSEventStreamCreate` is released.
unsafe extern "C-unwind" fn release_context(info: *const libc::c_void) {
    // Safety:
    // - The [documentation] for `FSEventStreamContext` states that `release` is only
    //   called when the stream is deallocated, so it is safe to convert `info` back into a
    //   box and drop it.
    //
    // [docs]: https://developer.apple.com/documentation/coreservices/fseventstreamcontext?language=objc
    unsafe {
        drop(Box::from_raw(
            info as *const StreamContextInfo as *mut StreamContextInfo,
        ));
    }
}

// Runs on the watcher thread, inside the running runloop, where
// `CFRunLoopStop` is guaranteed to take effect.
unsafe extern "C-unwind" fn stop_runloop_perform(_info: *mut std::ffi::c_void) {
    if let Some(runloop) = cf::CFRunLoop::current() {
        runloop.stop();
    }
}

// What the flush source's perform needs. Owned by the runloop thread, which
// invalidates the source before dropping it.
struct FlushSourceInfo {
    stream: fs::FSEventStreamRef,
    progress: Arc<StreamProgress>,
    stream_number: u64,
}

// Runs on the watcher thread, the thread the stream is scheduled on, so the
// stream is only ever touched there. `FSEventStreamFlushAsync` asks the service
// to send everything it holds back for `latency`; those events then reach the
// callback through this runloop like any other delivery, after this perform
// returns. No lock is held across the call, because the callback takes
// `progress.state` too.
unsafe extern "C-unwind" fn flush_stream_perform(info: *mut std::ffi::c_void) {
    let info = unsafe { &*(info as *const FlushSourceInfo) };
    let generation = lock_ignoring_poison(&info.progress.state).pending();
    let queued = unsafe { fs::FSEventStreamFlushAsync(info.stream) };
    let delivered = {
        let mut state = lock_ignoring_poison(&info.progress.state);
        state.answer(generation, queued);
        state.delivered
    };
    info.progress.changed.notify_all();
    fsevent_debug!(
        "stream {}: FSEventStreamFlushAsync returned {queued} (delivered so far {delivered}, \
         current event id {})",
        info.stream_number,
        unsafe { fs::FSEventsGetCurrentEventId() }
    );
}

impl FsEventWatcher {
    fn from_event_handler(
        event_handler: Arc<Mutex<dyn EventHandler>>,
        event_kinds: EventKindMask,
        latency: cf::CFTimeInterval,
    ) -> Result<Self> {
        Ok(FsEventWatcher {
            since_when: fs::kFSEventStreamEventIdSinceNow,
            latency,
            flags: fs::kFSEventStreamCreateFlagFileEvents
                | fs::kFSEventStreamCreateFlagNoDefer
                | fs::kFSEventStreamCreateFlagWatchRoot,
            event_handler,
            runloop: None,
            watches: HashMap::new(),
            event_kinds,
            swap_mechanism: SwapMechanism::FlushAndReplay,
            devices_with_history: HashSet::new(),
            root_identities: Arc::default(),
        })
    }

    fn watch_inner(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        let call_started_event_id = unsafe { fs::FSEventsGetCurrentEventId() };
        let result = self.append_path(path, recursive_mode);
        self.restart(call_started_event_id)?;
        result
    }

    fn unwatch_inner(&mut self, path: &Path) -> Result<()> {
        let call_started_event_id = unsafe { fs::FSEventsGetCurrentEventId() };
        let result = self.remove_path(path);
        self.restart(call_started_event_id)?;
        result
    }

    fn update_paths_inner(
        &mut self,
        ops: Vec<crate::PathOp>,
    ) -> crate::StdResult<(), crate::UpdatePathsError> {
        let call_started_event_id = unsafe { fs::FSEventsGetCurrentEventId() };
        let result = crate::update_paths(ops, |op| match op {
            crate::PathOp::Watch(path, config) => self
                .append_path(&path, config.recursive_mode())
                .map_err(|e| (PathOp::Watch(path, config), e)),
            crate::PathOp::Unwatch(path) => self
                .remove_path(&path)
                .map_err(|e| (PathOp::Unwatch(path), e)),
        });

        match self.restart(call_started_event_id) {
            Err(run_error) => match result {
                Ok(()) => Err(crate::UpdatePathsError {
                    source: run_error,
                    origin: None,
                    remaining: Default::default(),
                }),
                Err(path_op_error) => {
                    log::error!(
                        "Unable to run fsevents watcher after updating paths error: {run_error:?}"
                    );
                    Err(path_op_error)
                }
            },
            Ok(()) => result,
        }
    }

    #[inline]
    fn is_running(&self) -> bool {
        self.runloop.is_some()
    }

    // Replace the running stream (if any) with one watching the current path
    // set. The new stream is started before the old one is stopped, so that a
    // stream is watching at every moment: events firing inside a stop-then-start
    // window would be silently dropped for every watched path, not just the one
    // being (un)watched. Stopping a stream also drops whatever it still holds
    // back for `latency` and any delivery its runloop has not run yet. The new
    // stream therefore resumes from the last event id the old one delivered
    // (see `replay_since` and `ReplayFilter`), and the old one is flushed (see
    // `flush_handle`) before it is stopped, which is all that is left where the
    // volume keeps no history. An event can be delivered through both streams
    // during the swap; duplicates are fine, losses are not. If the new stream
    // fails to start, the old one is kept running so the previous path set
    // keeps delivering events.
    // `call_started_event_id` is the current event id sampled before the watch
    // call changed the watch set.
    fn restart(&mut self, call_started_event_id: fs::FSEventStreamEventId) -> Result<()> {
        let old_runloop = self.runloop.take();
        let replay = old_runloop
            .as_ref()
            .and_then(|handle| self.replay_filter(handle, call_started_event_id));
        let replaying = replay.is_some();
        let mut result = self.run(replay);
        if replaying && let Err(error) = &result {
            log::warn!(
                "FSEvents stream resuming from history did not start ({error:?}); starting from now"
            );
            result = self.run(None);
        }
        match &result {
            Ok(()) => {
                if let Some(handle) = old_runloop {
                    // With no replacement stream there is nobody to hand over to,
                    // and the remaining paths were all unwatched.
                    if self.runloop.is_some()
                        && self.swap_mechanism.flushes()
                        && !Self::flush_handle(&handle, FLUSH_TIMEOUT)
                    {
                        log::warn!(
                            "FSEvents stream did not flush within {FLUSH_TIMEOUT:?}; events it held back may be lost"
                        );
                    }
                    let watched_roots = Self::stop_handle(handle);
                    self.report_root_changes_held_by(&watched_roots);
                }
            }
            Err(_) => {
                debug_assert!(self.runloop.is_none());
                self.runloop = old_runloop;
            }
        }
        result
    }

    // Where the stream replacing `previous` resumes, or `None` to start it from
    // now.
    fn replay_filter(
        &mut self,
        previous: &RunLoopHandle,
        call_started_event_id: fs::FSEventStreamEventId,
    ) -> Option<ReplayFilter> {
        let swap_event_id = unsafe { fs::FSEventsGetCurrentEventId() };
        let hold_window = Duration::try_from_secs_f64(self.latency)
            .unwrap_or(Duration::ZERO)
            .saturating_add(REPLAY_GRACE);
        let (delivered, may_hold_events) = {
            let mut state = lock_ignoring_poison(&previous.progress.state);
            state.retiring = true;
            (
                state.delivered,
                state.may_hold_events(Instant::now(), hold_window),
            )
        };
        fsevent_debug!(
            "swap from stream {}: current event id {swap_event_id}, old stream delivered up to \
             {delivered}, may hold events: {may_hold_events}, mechanism {:?}",
            previous.stream_number,
            self.swap_mechanism
        );
        if !self.swap_mechanism.replays() {
            return None;
        }
        if let Some(device) = self.device_without_history() {
            log::info!(
                "FSEvents keeps no event history for device {device}; the replacement stream \
                 starts from now, and only the flush covers events the old stream held"
            );
            return None;
        }
        let since_when = replay_since(delivered, swap_event_id, may_hold_events)?;
        Some(ReplayFilter {
            since_when,
            swap_event_id: call_started_event_id.min(swap_event_id),
            previous_watches: previous.recursive_info.clone(),
            previous_progress: previous.progress.clone(),
            previous_stream: previous.stream_number,
        })
    }

    // A replay reads the event store of every volume the stream watches; one
    // without a store (`FSEventsCopyUUIDForDevice` returns NULL, for example a
    // read-only volume) has no history to replay. Only a store that exists is
    // cached: a volume can gain one, for example when it is remounted
    // read-write, and asking again costs one call per swap.
    fn device_without_history(&mut self) -> Option<u64> {
        for entry in self.watches.values() {
            if self.devices_with_history.contains(&entry.device) {
                continue;
            }
            let has_history = libc::dev_t::try_from(entry.device)
                .is_ok_and(|device| unsafe { fs::FSEventsCopyUUIDForDevice(device).is_some() });
            if !has_history {
                return Some(entry.device);
            }
            self.devices_with_history.insert(entry.device);
        }
        None
    }

    fn stop(&mut self) {
        if !self.is_running() {
            return;
        }

        if let Some(handle) = self.runloop.take() {
            Self::stop_handle(handle);
        }
    }

    // Has the old stream hand everything it holds to the event handler, and waits
    // until the handler is through it. Returns false if that did not happen
    // within `timeout`.
    //
    // The stream is flushed on its own runloop thread, which is alive until
    // `stop_handle` signals it, so the request cannot be lost. Only the caller of
    // `watch`/`unwatch` blocks, never the runloop; if that caller is the runloop
    // thread itself (a watch call from inside the event handler) waiting would
    // deadlock, so the flush is skipped.
    fn flush_handle(handle: &RunLoopHandle, timeout: Duration) -> bool {
        if handle.thread_handle.thread().id() == thread::current().id() {
            return false;
        }
        let deadline = Instant::now() + timeout;
        // Requested before signalling, so a completion of an earlier flush cannot
        // satisfy this one.
        let generation = lock_ignoring_poison(&handle.progress.state).request();
        handle.flush_source.signal();
        handle.runloop.wake_up();

        let mut state = lock_ignoring_poison(&handle.progress.state);
        while !state.is_complete(generation) {
            let remaining = deadline.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                return false;
            }
            state = handle
                .progress
                .changed
                .wait_timeout(state, remaining)
                .unwrap_or_else(|poisoned| poisoned.into_inner())
                .0;
        }
        true
    }

    // Returns the roots the stream watched, for `report_root_changes_held_by`.
    fn stop_handle(handle: RunLoopHandle) -> Vec<PathBuf> {
        let RunLoopHandle {
            runloop,
            stop_source,
            thread_handle,
            progress,
            watched_roots,
            stream_number,
            ..
        } = handle;
        {
            // Calling `CFRunLoopStop` directly here would race: it only takes effect
            // while the runloop is actually running, so a stop landing in the window
            // before the watcher thread enters `CFRunLoopRun` would be lost and the
            // `join` below would deadlock. Signaling a runloop source instead is
            // sticky: the signal stays pending until the loop runs, and the source's
            // `perform` callback then stops the loop from the inside, where the stop
            // cannot be lost. The wake-up covers the case where the loop is already
            // asleep.
            stop_source.signal();
            runloop.wake_up();
            // Wait for the thread to shut down.
            thread_handle.join().expect("thread to shut down");
        }
        fsevent_debug!(
            "stream {stream_number} stopped; last delivered id {}",
            lock_ignoring_poison(&progress.state).delivered
        );
        watched_roots
    }

    // Runs once the old stream has stopped, so every `RootChanged` event it
    // delivered has already updated `root_identities`; see `RootIdentity`.
    fn report_root_changes_held_by(&self, previous_roots: &[PathBuf]) {
        let changed_roots = {
            let mut identities = lock_ignoring_poison(&self.root_identities);
            take_unreported_root_changes(previous_roots, &mut identities, RootIdentity::of)
        };
        if changed_roots.is_empty() {
            return;
        }
        let mut event_handler = lock_ignoring_poison(&self.event_handler);
        for root in changed_roots {
            let Some(entry) = self.watches.get(root) else {
                continue;
            };
            fsevent_debug!(
                "root `{}` changed without a delivered RootChanged event; reporting it",
                root.display()
            );
            let event = Event::new(EventKind::Remove(RemoveKind::Any))
                .set_info("root changed")
                .add_path(entry.info.reported_path.clone());
            if self.event_kinds.matches(&event.kind) {
                event_handler.handle_event(Ok(event));
            }
        }
    }

    fn remove_path(&mut self, path: &Path) -> Result<()> {
        let p = path
            .canonicalize()
            .ok()
            .or_else(|| {
                self.watches
                    .iter()
                    .find(|(_, entry)| entry.info.reported_path == path)
                    .map(|(path, _)| path.clone())
            })
            .or_else(|| absolute_path(path).ok())
            .unwrap_or_else(|| path.to_owned());

        match self.watches.remove(&p) {
            Some(_) => {
                lock_ignoring_poison(&self.root_identities).remove(&p);
                Ok(())
            }
            None => Err(Error::watch_not_found()),
        }
    }

    // https://github.com/thibaudgg/rb-fsevent/blob/master/ext/fsevent_watch/main.c
    fn append_path(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        if !path.exists() {
            return Err(Error::path_not_found().add_path(path.into()));
        }
        let canonical_path = path.to_path_buf().canonicalize()?;
        let mut err: *mut cf::CFError = ptr::null_mut();
        let Some(cf_path) = (unsafe { path_to_cfstring_ref(&canonical_path, &mut err) }) else {
            if let Some(err) = NonNull::new(err) {
                let _ = unsafe { cf::CFRetained::from_raw(err) };
            }
            // Most likely the directory was deleted, or permissions changed,
            // while the above code was running.
            return Err(Error::path_not_found().add_path(path.into()));
        };

        let metadata = std::fs::metadata(&canonical_path)?;
        let device = metadata.dev();

        // A rewatch keeps the recorded identity: a change to the root before
        // it has not been reported yet.
        lock_ignoring_poison(&self.root_identities)
            .entry(canonical_path.clone())
            .or_insert_with(|| RootIdentity::from(&metadata));
        self.watches.insert(
            canonical_path,
            WatchEntry {
                info: WatchInfo {
                    is_recursive: recursive_mode.is_recursive(),
                    reported_path: path.to_path_buf(),
                },
                cf_path,
                device,
            },
        );
        Ok(())
    }

    // A recursive watch covers nested watches on the same volume. Non-recursive
    // ancestors may filter out deeper events, and FSEvents may not cross mounts.
    fn stream_roots(&self) -> impl Iterator<Item = (&PathBuf, &WatchEntry)> {
        self.watches.iter().filter(|(path, entry)| {
            !path.ancestors().skip(1).any(|ancestor| {
                self.watches.get(ancestor).is_some_and(|covering| {
                    covering.info.is_recursive && covering.device == entry.device
                })
            })
        })
    }

    #[cfg(test)]
    fn stream_paths(&self) -> cf::CFRetained<cf::CFMutableArray<cf::CFString>> {
        let paths: cf::CFRetained<cf::CFMutableArray<cf::CFString>> = cf::CFMutableArray::empty();
        for (_, entry) in self.stream_roots() {
            paths.append(&entry.cf_path);
        }
        paths
    }

    fn run(&mut self, replay: Option<ReplayFilter>) -> Result<()> {
        let watches_roots = self.flags & fs::kFSEventStreamCreateFlagWatchRoot != 0;
        let stream_paths: cf::CFRetained<cf::CFMutableArray<cf::CFString>> =
            cf::CFMutableArray::empty();
        let mut watched_roots = Vec::new();
        for (path, entry) in self.stream_roots() {
            stream_paths.append(&entry.cf_path);
            if watches_roots {
                watched_roots.push(path.clone());
            }
        }
        if stream_paths.is_empty() {
            return Ok(());
        }

        // Over roughly RLIMIT_NOFILE/10 paths across all live streams, FSEvents
        // closes fd 0, which this process owns. The corruption then surfaces as
        // EBADF on unrelated files.
        let path_count = stream_paths.iter().count();
        let budget = fsevents_path_budget().unwrap_or(usize::MAX);
        let path_reservation =
            match FseventsPathReservation::acquire(&ACTIVE_FSEVENTS_PATHS, path_count, budget) {
                Ok(reservation) => reservation,
                Err(active_path_count) => {
                    let combined_path_count = active_path_count.saturating_add(path_count);
                    log::error!(
                        "refusing FSEvents stream: {combined_path_count} active paths exceed the \
                         safe limit of {budget}. Raise RLIMIT_NOFILE, watch fewer paths, or use \
                         macos_kqueue."
                    );
                    return Err(Error::new(ErrorKind::MaxFilesWatch));
                }
            };

        let since_when = replay
            .as_ref()
            .map_or(self.since_when, |replay| replay.since_when);
        // Sampled before the stream is created, so every event the stream will
        // deliver has a larger id.
        let start_event_id = if since_when == fs::kFSEventStreamEventIdSinceNow {
            unsafe { fs::FSEventsGetCurrentEventId() }
        } else {
            since_when
        };
        let progress = Arc::new(StreamProgress::new(start_event_id, replay.is_some()));
        let stream_number = NEXT_STREAM_NUMBER.fetch_add(1, Ordering::Relaxed);
        let recursive_info: Arc<HashMap<PathBuf, WatchInfo>> = Arc::new(
            self.watches
                .iter()
                .map(|(path, entry)| (path.clone(), entry.info.clone()))
                .collect(),
        );
        if debug_logging_enabled() {
            match &replay {
                Some(replay) => fsevent_debug!(
                    "stream {stream_number}: replacing stream {} with sinceWhen {since_when} \
                     (watch call at event id {}), {path_count} paths",
                    replay.previous_stream,
                    replay.swap_event_id
                ),
                None => fsevent_debug!(
                    "stream {stream_number}: sinceWhen {} (current event id {start_event_id}), \
                     {path_count} paths",
                    if since_when == fs::kFSEventStreamEventIdSinceNow {
                        "now".to_string()
                    } else {
                        since_when.to_string()
                    }
                ),
            }
        }

        // We need to associate the stream context with our callback in order to propagate events
        // to the rest of the system. This will be owned by the stream, and will be freed when the
        // stream is closed. This means we will leak the context if we panic before reaching
        // `FSEventStreamRelease`.
        let context = Box::into_raw(Box::new(StreamContextInfo {
            event_handler: self.event_handler.clone(),
            recursive_info: recursive_info.clone(),
            event_kinds: self.event_kinds,
            progress: progress.clone(),
            replay: Mutex::new(replay),
            root_identities: self.root_identities.clone(),
            stream_number,
        }));

        let stream_context = fs::FSEventStreamContext {
            version: 0,
            info: context as *mut libc::c_void,
            retain: None,
            release: Some(release_context),
            copyDescription: None,
        };

        let stream = unsafe {
            fs::FSEventStreamCreate(
                cf::kCFAllocatorDefault,
                Some(callback),
                &stream_context as *const _ as *mut _,
                stream_paths.as_opaque(),
                since_when,
                self.latency,
                self.flags,
            )
        };

        // Wrapper to help send CFRunLoop types across threads.
        struct CFRunLoopSendWrapper(
            cf::CFRetained<cf::CFRunLoop>,
            cf::CFRetained<cf::CFRunLoopSource>,
            cf::CFRetained<cf::CFRunLoopSource>,
        );

        // Safety:
        // - According to the Apple documentation, it's safe to move `CFRunLoop`s and
        //   `CFRunLoopSource`s across threads.
        //   https://developer.apple.com/library/archive/documentation/Cocoa/Conceptual/Multithreading/ThreadSafetySummary/ThreadSafetySummary.html
        unsafe impl Send for CFRunLoopSendWrapper {}

        // Wrapper to help send FSEventStreamRef types across threads.
        struct FSEventStreamSendWrapper(fs::FSEventStreamRef);

        // TODO: Write docs for the safety of this impl.
        // SAFETY: Unclear?
        unsafe impl Send for FSEventStreamSendWrapper {}

        // move into thread
        let stream = FSEventStreamSendWrapper(stream);

        // channel to pass runloop around
        let (rl_tx, rl_rx) = unbounded();

        let flush_progress = progress.clone();
        let thread_handle = thread::Builder::new()
            .name("notify-rs fsevents loop".to_string())
            .spawn(move || {
                // Keep the shared path count reserved until this stream is released.
                let _path_reservation = path_reservation;
                let _ = &stream;
                let stream = stream.0;

                unsafe {
                    // Safety:
                    // This may panic if OOM occurs.
                    // Related: https://github.com/madsmtm/objc2/issues/797
                    let cur_runloop =
                        cf::CFRunLoop::current().expect("Failed to get current runloop");

                    #[allow(deprecated)]
                    fs::FSEventStreamScheduleWithRunLoop(
                        stream,
                        &cur_runloop,
                        cf::kCFRunLoopDefaultMode.expect("Failed to get default runloop mode"),
                    );
                    if !fs::FSEventStreamStart(stream) {
                        fs::FSEventStreamInvalidate(stream);
                        fs::FSEventStreamRelease(stream);
                        rl_tx
                            .send(Err(Error::generic("unable to start FSEvent stream")))
                            .expect("Unable to send error for FSEventStreamStart");
                        return;
                    }

                    // The source through which stop() asks this thread to shut down. It
                    // must be created and added to the runloop before the handles are
                    // published below, so the caller can never signal a source that is
                    // not registered yet.
                    let mut stop_source_context = cf::CFRunLoopSourceContext {
                        version: 0,
                        info: ptr::null_mut(),
                        retain: None,
                        release: None,
                        copyDescription: None,
                        equal: None,
                        hash: None,
                        schedule: None,
                        cancel: None,
                        perform: Some(stop_runloop_perform),
                    };
                    let stop_source = cf::CFRunLoopSource::new(
                        cf::kCFAllocatorDefault,
                        0,
                        &mut stop_source_context,
                    )
                    .expect("Failed to create stop source");
                    cur_runloop.add_source(Some(&stop_source), cf::kCFRunLoopDefaultMode);

                    // The source through which `restart` asks this thread to flush the
                    // stream before it is replaced; see `flush_handle`. `flush_info`
                    // outlives the source, which is invalidated before it is dropped.
                    let mut flush_info = FlushSourceInfo {
                        stream,
                        progress: flush_progress,
                        stream_number,
                    };
                    let mut flush_source_context = cf::CFRunLoopSourceContext {
                        version: 0,
                        info: &mut flush_info as *mut FlushSourceInfo as *mut libc::c_void,
                        retain: None,
                        release: None,
                        copyDescription: None,
                        equal: None,
                        hash: None,
                        schedule: None,
                        cancel: None,
                        perform: Some(flush_stream_perform),
                    };
                    let flush_source = cf::CFRunLoopSource::new(
                        cf::kCFAllocatorDefault,
                        0,
                        &mut flush_source_context,
                    )
                    .expect("Failed to create flush source");
                    cur_runloop.add_source(Some(&flush_source), cf::kCFRunLoopDefaultMode);

                    // `stop()` will signal `stop_source`, wake the runloop, and then join
                    // this thread.
                    rl_tx
                        .send(Ok(CFRunLoopSendWrapper(
                            cur_runloop,
                            stop_source.clone(),
                            flush_source.clone(),
                        )))
                        .expect("Unable to send runloop to watcher");

                    // Block until the pending signal on `stop_source` (if any) or a later
                    // one stops the loop from the inside; see `stop()`.
                    cf::CFRunLoop::run();

                    flush_source.invalidate();
                    drop(flush_info);
                    stop_source.invalidate();
                    fs::FSEventStreamStop(stream);
                    fs::FSEventStreamInvalidate(stream);
                    fs::FSEventStreamRelease(stream);
                }
            })?;
        // block until runloop has been sent
        let runloop_wrapper = match rl_rx.recv() {
            Ok(Ok(runloop_wrapper)) => runloop_wrapper,
            Ok(Err(err)) => {
                thread_handle
                    .join()
                    .expect("thread to shut down after FSEvent stream startup failure");
                return Err(err);
            }
            Err(_) => {
                thread_handle
                    .join()
                    .expect("thread to shut down after FSEvent stream startup channel close");
                return Err(Error::generic(
                    "unable to receive FSEvent stream startup result",
                ));
            }
        };
        self.runloop = Some(RunLoopHandle {
            runloop: runloop_wrapper.0,
            stop_source: runloop_wrapper.1,
            flush_source: runloop_wrapper.2,
            thread_handle,
            progress,
            recursive_info,
            watched_roots,
            stream_number,
        });

        Ok(())
    }

    fn configure_raw_mode(&mut self, _config: Config, tx: Sender<Result<bool>>) {
        tx.send(Ok(false))
            .expect("configuration channel disconnect");
    }
}

// A twelfth rather than a tenth: the edge also shifts with how many descriptors
// the process already holds.
fn fsevents_path_budget() -> Option<usize> {
    let mut limit = unsafe { std::mem::zeroed::<libc::rlimit>() };
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut limit) } != 0 {
        return None;
    }
    let soft = usize::try_from(limit.rlim_cur).ok()?;
    Some(soft / 12)
}

unsafe extern "C-unwind" fn callback(
    stream_ref: fs::ConstFSEventStreamRef,
    info: *mut libc::c_void,
    num_events: libc::size_t,                          // size_t numEvents
    event_paths: NonNull<libc::c_void>,                // void *eventPaths
    event_flags: NonNull<fs::FSEventStreamEventFlags>, // const FSEventStreamEventFlags eventFlags[]
    event_ids: NonNull<fs::FSEventStreamEventId>,      // const FSEventStreamEventId eventIds[]
) {
    // Never unwind into CoreServices; if something goes wrong, drop the events and log.
    // This also protects against panics from user-provided `EventHandler` implementations.
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| unsafe {
        callback_impl(
            stream_ref,
            info,
            num_events,
            event_paths,
            event_flags,
            event_ids,
        )
    }))
    .map_err(|_| {
        log::error!("panic in FSEvents callback; dropping pending events");
    });
}

unsafe fn callback_impl(
    _stream_ref: fs::ConstFSEventStreamRef,
    info: *mut libc::c_void,
    num_events: libc::size_t,                          // size_t numEvents
    event_paths: NonNull<libc::c_void>,                // void *eventPaths
    event_flags: NonNull<fs::FSEventStreamEventFlags>, // const FSEventStreamEventFlags eventFlags[]
    event_ids: NonNull<fs::FSEventStreamEventId>,      // const FSEventStreamEventId eventIds[]
) {
    let event_paths = event_paths.as_ptr() as *const *const libc::c_char;
    let info = info as *const StreamContextInfo;
    let event_handler_mutex = &(*info).event_handler;
    let event_kinds = (*info).event_kinds;
    let mut replay_guard = lock_ignoring_poison(unsafe { &(*info).replay });
    let replay = replay_guard.as_ref();
    let progress = unsafe { &(*info).progress };
    let event_ids = unsafe { std::slice::from_raw_parts(event_ids.as_ptr(), num_events) };
    let mut event_handler_guard = None;
    let mut history_done = false;
    let mut highest_id = None;

    let previous_delivered =
        replay.map(|replay| lock_ignoring_poison(&replay.previous_progress.state).delivered);
    let debug = debug_logging_enabled();
    if debug {
        let role = if lock_ignoring_poison(&progress.state).retiring {
            "old"
        } else if replay.is_some() {
            "new"
        } else {
            "live"
        };
        fsevent_debug!(
            "stream {} ({role}): batch of {num_events}, ids {:?}..{:?}",
            unsafe { (*info).stream_number },
            event_ids.first(),
            event_ids.last()
        );
    }

    for (index, &event_id) in event_ids.iter().enumerate() {
        // Paths are not guaranteed to be valid UTF-8 (e.g. NFS); keep them as raw bytes.
        let path = CStr::from_ptr(*event_paths.add(index));
        let path = Path::new(OsStr::from_bytes(path.to_bytes()));

        let raw_flag = *event_flags.as_ptr().add(index) as u32;
        let flag = StreamFlags::from_bits_truncate(raw_flag);
        let unknown_bits = raw_flag & !StreamFlags::all().bits();
        if unknown_bits != 0 {
            // `FSEventStreamEventFlags` is an extensible bitfield; tolerate future flags.
            log::trace!("unknown FSEventStreamEventFlags bits: 0x{unknown_bits:08x}");
        }

        let skip = if flag.contains(StreamFlags::HISTORY_DONE) {
            // The sentinel's id is not an event's.
            history_done = true;
            Some("history done")
        } else {
            highest_id = highest_id.max(Some(event_id));
            replay
                .zip(previous_delivered)
                .and_then(|(replay, previous_delivered)| {
                    replay
                        .skip(path, event_id, previous_delivered)
                        .map(|skip| match skip {
                            ReplaySkip::PredatesWatch => "replayed, predates the watch",
                            ReplaySkip::AlreadyDelivered => "replayed, old stream delivered it",
                        })
                })
        };
        if debug {
            fsevent_debug!(
                "stream {}:   id {event_id} flags {flag:?} (0x{raw_flag:08x}) path `{}`{}",
                unsafe { (*info).stream_number },
                path.display(),
                skip.map(|reason| format!(" -> skipped: {reason}"))
                    .unwrap_or_default()
            );
        }
        if skip.is_some() {
            continue;
        }
        // Before the event reaches the handler, so a change after the stat is
        // still caught by the next swap's comparison.
        if flag.contains(StreamFlags::ROOT_CHANGED) {
            record_root_identity(path, unsafe { &(*info).root_identities });
        }

        let Some((watch_path, watch_info)) = find_watch(path, unsafe { &(*info).recursive_info })
        else {
            continue;
        };
        let translated_count = translated_event_count(&flag, true);
        if translated_count == 0 {
            continue;
        }
        // Most FSEvents flags produce one Event; move the reported path in that case.
        let mut event_path = Some(reported_path(watch_path, &watch_info.reported_path, path));
        let single_translated_event = translated_count == 1;

        log::trace!("FSEvent: path = `{}`, flag = {:?}", path.display(), flag);

        translate_flags_with(flag, true, |mut ev| {
            // Filter events based on EventKindMask before adding the path.
            if !event_kinds.matches(&ev.kind) {
                return;
            }
            if single_translated_event {
                ev.paths.push(
                    event_path.take().unwrap_or_else(|| {
                        reported_path(watch_path, &watch_info.reported_path, path)
                    }),
                );
            } else {
                ev.paths
                    .push(event_path.as_ref().expect("translated event path").clone());
            }

            let event_handler =
                event_handler_guard.get_or_insert_with(|| match event_handler_mutex.lock() {
                    Ok(guard) => guard,
                    Err(poisoned) => poisoned.into_inner(),
                });
            // Protect against panicking event handlers, which would otherwise unwind into
            // the CoreServices callback.
            let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                event_handler.handle_event(Ok(ev));
            }))
            .map_err(|_| {
                log::error!("panic in FSEvents event handler; dropping event");
            });
        });
    }

    // Recorded only once the handler is through the whole batch, and after its
    // lock is released, so a waiting `flush_handle` never sees a delivery that
    // is still in progress, and a replacement stream that resumes from it can
    // only repeat, never skip, an event from this batch.
    drop(event_handler_guard);
    if history_done && let Some(replay) = replay_guard.take() {
        fsevent_debug!(
            "stream {}: history replay since {} done",
            unsafe { (*info).stream_number },
            replay.since_when
        );
    }
    drop(replay_guard);
    if highest_id.is_some() || history_done {
        {
            let mut state = lock_ignoring_poison(&progress.state);
            if let Some(highest_id) = highest_id {
                state.record_delivery(highest_id, Instant::now());
            }
            if history_done {
                state.history_pending = false;
            }
        }
        progress.changed.notify_all();
    }
}

// The deepest watch that covers `path`: a recursive watch covers its whole
// subtree, a non-recursive one only itself and its direct children.
fn find_watch<'a>(
    path: &Path,
    watches: &'a HashMap<PathBuf, WatchInfo>,
) -> Option<(&'a PathBuf, &'a WatchInfo)> {
    let mut watch_match: Option<(&PathBuf, &WatchInfo)> = None;
    for (watch_path, watch_info) in watches {
        if path.starts_with(watch_path) {
            let matches_watch = if watch_info.is_recursive || path == watch_path {
                true
            } else if let Some(parent_path) = path.parent() {
                parent_path == watch_path
            } else {
                false
            };

            if matches_watch
                && watch_match.is_none_or(|(matched_path, _)| {
                    watch_path.as_os_str().as_bytes().len()
                        > matched_path.as_os_str().as_bytes().len()
                })
            {
                watch_match = Some((watch_path, watch_info));
            }
        }
    }
    watch_match
}

impl Watcher for FsEventWatcher {
    /// Create a new watcher.
    fn new<F: EventHandler>(event_handler: F, config: Config) -> Result<Self> {
        Self::from_event_handler(
            Arc::new(Mutex::new(event_handler)),
            config.event_kinds(),
            config.fsevent_latency().as_secs_f64(),
        )
    }

    fn watch(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.watch_inner(path, recursive_mode)
    }

    fn unwatch(&mut self, path: &Path) -> Result<()> {
        self.unwatch_inner(path)
    }

    fn update_paths(&mut self, ops: Vec<PathOp>) -> crate::StdResult<(), crate::UpdatePathsError> {
        self.update_paths_inner(ops)
    }

    fn configure(&mut self, config: Config) -> Result<bool> {
        let (tx, rx) = unbounded();
        self.configure_raw_mode(config, tx);
        rx.recv()?
    }

    fn watched_paths(&self) -> Result<Vec<(PathBuf, RecursiveMode)>> {
        // Unlike the channel-based backends, FSEvents keeps watch state on the watcher itself.
        // The runloop callback gets a cloned snapshot in `StreamContextInfo`, so it does not
        // mutate or read this map concurrently.
        Ok(self
            .watches
            .iter()
            .map(|(_path, WatchEntry { info, .. })| {
                (
                    info.reported_path.clone(),
                    if info.is_recursive {
                        RecursiveMode::Recursive
                    } else {
                        RecursiveMode::NonRecursive
                    },
                )
            })
            .collect())
    }

    fn kind() -> crate::WatcherKind {
        crate::WatcherKind::Fsevent
    }
}

impl Drop for FsEventWatcher {
    fn drop(&mut self) {
        self.stop();
    }
}

/// Grabbed from <https://docs.rs/fsevent-sys/4.1.0/src/fsevent_sys/core_foundation.rs.html#149-230>.
///
/// TODO: Could we simplify this?
unsafe fn path_to_cfstring_ref(
    source: &Path,
    err: &mut *mut cf::CFError,
) -> Option<cf::CFRetained<cf::CFString>> {
    let url = cf::CFURL::from_file_path(source)?;

    let mut placeholder = url.absolute_url()?;

    let imaginary = cf::CFMutableArray::empty();

    while !unsafe { placeholder.resource_is_reachable(err) } {
        if let Some(child) = placeholder.last_path_component() {
            imaginary.insert(0, &*child);
        }

        placeholder = cf::CFURL::new_copy_deleting_last_path_component(None, Some(&placeholder))?;
    }

    let url = unsafe { cf::CFURL::new_file_reference_url(None, Some(&placeholder), err) }?;

    let mut placeholder = unsafe { cf::CFURL::new_file_path_url(None, Some(&url), err) }?;

    for component in imaginary {
        placeholder = cf::CFURL::new_copy_appending_path_component(
            None,
            Some(&placeholder),
            Some(&component),
            false,
        )?;
    }

    placeholder.file_system_path(cf::CFURLPathStyle::CFURLPOSIXPathStyle)
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use crate::{ErrorKind, WatchPathConfig};

    use super::*;
    use crate::test::*;

    fn watcher() -> (TestWatcher<FsEventWatcher>, Receiver) {
        channel()
    }

    #[test]
    fn rewatching_same_path_replaces_recursive_info() {
        let dir = tempfile::tempdir().unwrap();
        let mut watcher = FsEventWatcher::new(|_| {}, Config::default()).unwrap();

        watcher
            .append_path(dir.path(), RecursiveMode::Recursive)
            .expect("watch recursively");
        watcher
            .append_path(dir.path(), RecursiveMode::NonRecursive)
            .expect("rewatch non-recursively");

        let watched = watcher.watched_paths().expect("watched paths");
        assert_eq!(
            watched,
            vec![(dir.path().to_path_buf(), RecursiveMode::NonRecursive)]
        );
        assert_eq!(watcher.stream_paths().iter().count(), 1);
    }

    #[test]
    fn only_recursive_ancestors_cover_nested_watches() {
        let dir = tempfile::tempdir().unwrap();
        let child = dir.path().join("child");
        let grandchild = child.join("first").join("second").join("grandchild");
        std::fs::create_dir_all(&grandchild).unwrap();

        let mut watcher = FsEventWatcher::new(|_| {}, Config::default()).unwrap();
        for (path, mode) in [
            (dir.path(), RecursiveMode::Recursive),
            (child.as_path(), RecursiveMode::NonRecursive),
            (grandchild.as_path(), RecursiveMode::Recursive),
        ] {
            watcher.append_path(path, mode).expect("watch");
        }

        assert_eq!(watcher.stream_paths().iter().count(), 1);
        assert_eq!(watcher.watched_paths().expect("watched paths").len(), 3);

        watcher.remove_path(dir.path()).expect("unwatch parent");
        // The remaining non-recursive child would discard changes to the deeper
        // watch's intermediate ancestors, so both watches need stream roots.
        assert_eq!(watcher.stream_paths().iter().count(), 2);

        watcher.remove_path(&child).expect("unwatch child");
        assert_eq!(watcher.stream_paths().iter().count(), 1);
    }

    #[test]
    fn sibling_watches_each_get_a_stream_root() {
        let dir = tempfile::tempdir().unwrap();
        let first = dir.path().join("first");
        let second = dir.path().join("second");
        std::fs::create_dir(&first).unwrap();
        std::fs::create_dir(&second).unwrap();

        let mut watcher = FsEventWatcher::new(|_| {}, Config::default()).unwrap();
        watcher
            .append_path(&first, RecursiveMode::Recursive)
            .expect("watch first");
        watcher
            .append_path(&second, RecursiveMode::Recursive)
            .expect("watch second");

        assert_eq!(watcher.stream_paths().iter().count(), 2);
    }

    #[test]
    fn covering_watch_keeps_receiving_outside_the_nested_watch() {
        let tmpdir = testdir();
        let child = tmpdir.path().join("child");
        let sibling = tmpdir.path().join("sibling");
        std::fs::create_dir(&child).expect("create child");
        std::fs::create_dir(&sibling).expect("create sibling");

        let (mut watcher, mut rx) = watcher();
        watcher.watch_recursively(&tmpdir);
        watcher.watch_recursively(&child);

        let path = sibling.join("entry");
        std::fs::File::create_new(&path).expect("create");

        rx.wait_unordered([expected(path).create_file()]);
    }

    #[test]
    fn nested_watch_keeps_receiving_after_unwatching_its_parent() {
        let tmpdir = testdir();
        let child = tmpdir.path().join("child");
        std::fs::create_dir(&child).expect("create dir");

        let (mut watcher, mut rx) = watcher();
        watcher.watch_recursively(&tmpdir);
        watcher.watch_recursively(&child);
        watcher
            .watcher
            .unwatch(tmpdir.path())
            .expect("unwatch parent");

        let path = child.join("entry");
        std::fs::File::create_new(&path).expect("create");

        rx.wait_unordered([expected(path).create_file()]);
    }

    // With `NoDefer`, the first event after a quiet period is delivered at once
    // and the next is held for the latency; watching another path in that
    // window replaces the stream, which must not drop the held event. The test
    // first waits a part of the latency and checks the event really is held:
    // by then the service has queued it for the old stream, so a new stream
    // starting from now cannot deliver it, only the old stream's flush or the
    // new stream's replay can. Only events on its own path count, so other
    // tests' FSEvents traffic cannot satisfy or fail it.
    fn assert_held_event_survives_a_stream_swap(mechanism: SwapMechanism) {
        const LATENCY: Duration = Duration::from_secs(3);
        const HELD_CHECK: Duration = Duration::from_secs(1);
        // A replayed event goes through the new stream's runloop after the
        // swap returns, and its delivery may itself be held for the latency.
        const AFTER_SWAP_MARGIN: Duration = Duration::from_secs(2);
        const LATE_ARRIVAL_WAIT: Duration = Duration::from_secs(10);

        let tmpdir = testdir();
        let watched = tmpdir.path().join("watched");
        let added = tmpdir.path().join("added");
        std::fs::create_dir(&watched).expect("create watched");
        std::fs::create_dir(&added).expect("create added");

        let (mut watcher, mut rx) = channel_with_config::<FsEventWatcher>(
            ChannelConfig::default()
                .with_timeout(Duration::from_secs(10))
                .with_watcher_config(Config::default().with_fsevent_latency(LATENCY)),
        );
        watcher.watcher.swap_mechanism = mechanism;
        watcher.watch_recursively(&watched);

        let first = watched.join("first");
        std::fs::File::create_new(&first).expect("create first");
        rx.wait_unordered([expected(&first).create_file()]);

        let held = watched.join("held");
        let is_held_creation = |event: &Event| expected(&held).create_file() == *event;
        std::fs::File::create_new(&held).expect("create held");
        let held_created = Instant::now();
        fsevent_debug!("test: created {}", held.display());

        let check_ends = held_created + HELD_CHECK;
        loop {
            let remaining = check_ends.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                break;
            }
            match rx.rx.recv_timeout(remaining) {
                Ok(Ok(event)) => assert!(
                    !is_held_creation(&event),
                    "the event was delivered {:?} after it happened, inside the {LATENCY:?} \
                     latency, so it was never held and the swap below proves nothing",
                    held_created.elapsed()
                ),
                Ok(Err(error)) => panic!("watcher error before the swap: {error:?}"),
                Err(_) => break,
            }
        }

        fsevent_debug!("test: swapping streams with {mechanism:?}");
        let swap_started = Instant::now();
        watcher.watch_recursively(&added);
        let swap_returned = Instant::now();
        let swap_took = swap_returned - swap_started;
        fsevent_debug!("test: swap took {swap_took:?}");

        let deadline = swap_returned + LATENCY + AFTER_SWAP_MARGIN;
        let late_arrival_ends = swap_returned + LATE_ARRIVAL_WAIT;
        loop {
            let remaining = late_arrival_ends.saturating_duration_since(Instant::now());
            match rx.rx.recv_timeout(remaining) {
                Ok(Ok(event)) if is_held_creation(&event) => {
                    let arrived = Instant::now();
                    fsevent_debug!(
                        "test: held event arrived {:?} after it happened, {:?} after the swap \
                         returned",
                        arrived - held_created,
                        arrived.saturating_duration_since(swap_returned)
                    );
                    assert!(
                        arrived <= deadline,
                        "the held event arrived {:?} after it happened and {:?} after the swap \
                         returned (the swap took {swap_took:?}), later than the {LATENCY:?} \
                         latency plus {AFTER_SWAP_MARGIN:?}",
                        arrived - held_created,
                        arrived - swap_returned
                    );
                    return;
                }
                Ok(Ok(_)) => {}
                Ok(Err(error)) => panic!("watcher error after the swap: {error:?}"),
                Err(_) => panic!(
                    "the held event was lost with {mechanism:?}: nothing for it \
                     {LATE_ARRIVAL_WAIT:?} after a swap that took {swap_took:?}"
                ),
            }
        }
    }

    #[test]
    fn event_held_for_latency_survives_a_stream_swap() {
        assert_held_event_survives_a_stream_swap(SwapMechanism::FlushAndReplay);
    }

    // The two mechanisms the swap combines, each alone, so a Mac run shows
    // which one delivers the held event. Run them with
    // `NOTIFY_FSEVENT_DEBUG=1 cargo test -p notify --lib held_event_with -- --ignored --nocapture`.
    #[test]
    #[ignore = "diagnostic: shows whether the flush alone delivers a held event"]
    fn held_event_with_flush_only_survives_a_stream_swap() {
        assert_held_event_survives_a_stream_swap(SwapMechanism::FlushOnly);
    }

    #[test]
    #[ignore = "diagnostic: shows whether the replay alone delivers a held event"]
    fn held_event_with_replay_only_survives_a_stream_swap() {
        assert_held_event_survives_a_stream_swap(SwapMechanism::ReplayOnly);
    }

    #[test]
    fn stop_does_not_wait_for_runloop_to_be_waiting() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::mpsc;
        use std::time::Instant;

        // Regression test for a shutdown hang where `stop()` waited for
        // `CFRunLoopIsWaiting()` to become true. If the runloop is busy (e.g. under
        // heavy event load), it may never enter a waiting state.

        let dir = tempfile::tempdir().unwrap();

        let (tx, _rx) = mpsc::channel::<crate::Result<Event>>();
        let mut watcher = FsEventWatcher::new(tx, Default::default()).unwrap();
        watcher.watch(dir.path(), RecursiveMode::Recursive).unwrap();

        let runloop = watcher
            .runloop
            .as_ref()
            .expect("watcher to be running")
            .runloop
            .clone();
        let mode = unsafe { cf::kCFRunLoopDefaultMode.expect("default runloop mode") };

        // Keep the runloop continuously "busy" by creating a source that signals itself in its
        // perform callback.
        struct SourceHammer {
            source: *const cf::CFRunLoopSource,
            fires: AtomicUsize,
        }

        unsafe extern "C-unwind" fn hammer_source(info: *mut std::ffi::c_void) {
            let Some(hammer) = (info as *const SourceHammer).as_ref() else {
                return;
            };
            hammer.fires.fetch_add(1, Ordering::Relaxed);

            // Signal the source again so the runloop has more work to do.
            let Some(source) = (hammer.source as *const cf::CFRunLoopSource).as_ref() else {
                return;
            };
            source.signal();
        }

        let mut hammer = Box::new(SourceHammer {
            source: std::ptr::null(),
            fires: AtomicUsize::new(0),
        });

        let mut ctx = cf::CFRunLoopSourceContext {
            version: 0,
            info: (&mut *hammer as *mut SourceHammer).cast(),
            retain: None,
            release: None,
            copyDescription: None,
            equal: None,
            hash: None,
            schedule: None,
            cancel: None,
            perform: Some(hammer_source),
        };

        let source = unsafe {
            cf::CFRunLoopSource::new(cf::kCFAllocatorDefault, 0, &mut ctx)
                .expect("source to be created")
        };
        hammer.source = cf::CFRetained::as_ptr(&source).as_ptr();

        runloop.add_source(Some(&source), Some(mode));
        source.signal();
        runloop.wake_up();

        // Ensure our setup actually made the runloop busy.
        let setup_start = Instant::now();
        while hammer.fires.load(Ordering::Relaxed) == 0
            && setup_start.elapsed() < Duration::from_secs(1)
        {
            std::thread::yield_now();
        }
        assert!(
            hammer.fires.load(Ordering::Relaxed) > 0,
            "runloop source never fired; test setup failed"
        );

        let (done_tx, done_rx) = mpsc::channel::<()>();
        std::thread::spawn(move || {
            drop(watcher);
            let _ = done_tx.send(());
        });

        // If shutdown regresses, this would hang indefinitely; keep the test bounded.
        done_rx
            .recv_timeout(Duration::from_secs(5))
            .expect("dropping FsEventWatcher timed out (possible shutdown hang)");

        // No cleanup: The source is owned by the runloop; removing sources cross-thread can be
        // sensitive on some systems. Dropping the last reference to the runloop will release it.
    }

    // Regression test for a lost `CFRunLoopStop`: stopping is a no-op while the
    // runloop thread is between publishing its handles and actually entering
    // `CFRunLoopRun`, so a single stop could leave the thread parked forever and
    // deadlock the join in `stop()`. Rapid watch/unwatch cycles maximize pressure
    // on that window.
    #[test]
    fn rapid_watch_unwatch_does_not_hang() {
        use std::sync::mpsc;

        let tmpdir = tempfile::tempdir().unwrap();
        let dir_a = tmpdir.path().join("a");
        let dir_b = tmpdir.path().join("b");
        std::fs::create_dir(&dir_a).expect("create_dir a");
        std::fs::create_dir(&dir_b).expect("create_dir b");

        let (done_tx, done_rx) = mpsc::channel::<()>();
        let stress_thread = thread::spawn(move || {
            let (tx, _rx) = mpsc::channel::<crate::Result<Event>>();
            let mut watcher = FsEventWatcher::new(tx, Default::default()).unwrap();
            for _ in 0..500 {
                // Errors are tolerated: under load (e.g. the 4096-path test running
                // concurrently) fseventsd transiently refuses stream starts even for
                // tiny path sets. The property under test is purely that none of
                // these operations hangs.
                let _ = watcher.watch(&dir_a, RecursiveMode::NonRecursive);
                let _ = watcher.watch(&dir_b, RecursiveMode::NonRecursive);
                let _ = watcher.unwatch(&dir_a);
                let _ = watcher.unwatch(&dir_b);
            }
            let _ = done_tx.send(());
        });

        done_rx
            .recv_timeout(Duration::from_secs(120))
            .expect("rapid watch/unwatch timed out (lost CFRunLoopStop?)");
        stress_thread.join().expect("stress thread to shut down");
    }

    // Deterministic test of the race window above: a stop source signaled
    // before `CFRunLoopRun` is entered must still stop the loop, because
    // source signals stay pending until the loop processes them.
    #[test]
    fn stop_source_signaled_before_runloop_run_still_stops_loop() {
        use std::sync::mpsc;

        struct CFSendWrapper<T: cf::Type>(cf::CFRetained<T>);
        unsafe impl<T: cf::Type> Send for CFSendWrapper<T> {}

        let (handles_tx, handles_rx) = mpsc::channel();
        let (signaled_tx, signaled_rx) = mpsc::channel::<()>();
        let (done_tx, done_rx) = mpsc::channel::<()>();

        let loop_thread = thread::spawn(move || {
            let cur_runloop = cf::CFRunLoop::current().expect("current runloop");

            let mut stop_source_context = cf::CFRunLoopSourceContext {
                version: 0,
                info: ptr::null_mut(),
                retain: None,
                release: None,
                copyDescription: None,
                equal: None,
                hash: None,
                schedule: None,
                cancel: None,
                perform: Some(stop_runloop_perform),
            };
            let stop_source = unsafe {
                cf::CFRunLoopSource::new(cf::kCFAllocatorDefault, 0, &mut stop_source_context)
                    .expect("stop source to be created")
            };
            let mode = unsafe { cf::kCFRunLoopDefaultMode.expect("default runloop mode") };
            cur_runloop.add_source(Some(&stop_source), Some(mode));

            handles_tx
                .send((
                    CFSendWrapper(cur_runloop),
                    CFSendWrapper(stop_source.clone()),
                ))
                .expect("send runloop handles");

            signaled_rx
                .recv()
                .expect("wait for the stop source to be signaled");

            cf::CFRunLoop::run();

            stop_source.invalidate();
            let _ = done_tx.send(());
        });

        let (runloop, stop_source) = handles_rx.recv().expect("receive runloop handles");
        stop_source.0.signal();
        runloop.0.wake_up();
        signaled_tx.send(()).expect("release the loop thread");

        done_rx
            .recv_timeout(Duration::from_secs(10))
            .expect("CFRunLoopRun did not exit; pre-run stop source signal was lost");
        loop_thread.join().expect("loop thread to shut down");
    }

    #[test]
    fn test_fsevent_watcher_drop() {
        use super::*;
        use std::time::Duration;

        let dir = tempfile::tempdir().unwrap();

        let (tx, rx) = std::sync::mpsc::channel();

        {
            let mut watcher = FsEventWatcher::new(tx, Default::default()).unwrap();
            watcher.watch(dir.path(), RecursiveMode::Recursive).unwrap();
            thread::sleep(Duration::from_millis(2000));
            println!("is running -> {}", watcher.is_running());

            thread::sleep(Duration::from_millis(1000));
            watcher.unwatch(dir.path()).unwrap();
            println!("is running -> {}", watcher.is_running());
        }

        thread::sleep(Duration::from_millis(1000));

        for res in rx {
            let e = res.unwrap();
            println!("debug => {:?} {:?}", e.kind, e.paths);
        }

        println!("in test: {} works", file!());
    }

    // The same setup as `assert_held_event_survives_a_stream_swap`, with the
    // watched root renamed instead of a file created inside it: the
    // `RootChanged` event this produces has id 0, so neither the flush nor the
    // replay can bring it back once the old stream is held and stopped.
    #[test]
    fn root_change_held_for_latency_survives_a_stream_swap() {
        const LATENCY: Duration = Duration::from_secs(3);
        const HELD_CHECK: Duration = Duration::from_secs(1);
        const AFTER_SWAP_MARGIN: Duration = Duration::from_secs(2);
        const LATE_ARRIVAL_WAIT: Duration = Duration::from_secs(10);

        let tmpdir = testdir();
        let root = tmpdir.path().join("root");
        let moved = tmpdir.path().join("moved");
        let added = tmpdir.path().join("added");
        std::fs::create_dir(&root).expect("create root");
        std::fs::create_dir(&added).expect("create added");

        let (mut watcher, mut rx) = channel_with_config::<FsEventWatcher>(
            ChannelConfig::default()
                .with_timeout(Duration::from_secs(10))
                .with_watcher_config(Config::default().with_fsevent_latency(LATENCY)),
        );
        watcher.watch_recursively(&root);

        let first = root.join("first");
        std::fs::File::create_new(&first).expect("create first");
        rx.wait_unordered([expected(&first).create_file()]);

        let is_root_change = |event: &Event| {
            event.info() == Some("root changed")
                && event.paths.as_slice() == std::slice::from_ref(&root)
        };
        std::fs::rename(&root, &moved).expect("rename root");
        let renamed = Instant::now();
        fsevent_debug!("test: renamed {} to {}", root.display(), moved.display());

        let check_ends = renamed + HELD_CHECK;
        loop {
            let remaining = check_ends.saturating_duration_since(Instant::now());
            if remaining.is_zero() {
                break;
            }
            match rx.rx.recv_timeout(remaining) {
                Ok(Ok(event)) => assert!(
                    !is_root_change(&event),
                    "the root change was delivered {:?} after the rename, inside the \
                     {LATENCY:?} latency, so it was never held and the swap below proves nothing",
                    renamed.elapsed()
                ),
                Ok(Err(error)) => panic!("watcher error before the swap: {error:?}"),
                Err(_) => break,
            }
        }

        fsevent_debug!("test: swapping streams");
        let swap_started = Instant::now();
        watcher.watch_recursively(&added);
        let swap_returned = Instant::now();
        let swap_took = swap_returned - swap_started;
        fsevent_debug!("test: swap took {swap_took:?}");

        let deadline = swap_returned + LATENCY + AFTER_SWAP_MARGIN;
        let late_arrival_ends = swap_returned + LATE_ARRIVAL_WAIT;
        loop {
            let remaining = late_arrival_ends.saturating_duration_since(Instant::now());
            match rx.rx.recv_timeout(remaining) {
                Ok(Ok(event)) if is_root_change(&event) => {
                    let arrived = Instant::now();
                    fsevent_debug!(
                        "test: root change arrived {:?} after the rename, {:?} after the swap \
                         returned: {event:?}",
                        arrived - renamed,
                        arrived.saturating_duration_since(swap_returned)
                    );
                    assert!(
                        arrived <= deadline,
                        "the root change arrived {:?} after the swap returned (the swap took \
                         {swap_took:?}), later than the {LATENCY:?} latency plus \
                         {AFTER_SWAP_MARGIN:?}",
                        arrived - swap_returned
                    );
                    return;
                }
                Ok(Ok(_)) => {}
                Ok(Err(error)) => panic!("watcher error after the swap: {error:?}"),
                Err(_) => panic!(
                    "the root change was lost: nothing for it {LATE_ARRIVAL_WAIT:?} after a \
                     swap that took {swap_took:?}"
                ),
            }
        }
    }

    #[test]
    fn root_change_is_reported_once_and_only_for_still_watched_roots() {
        let replaced = PathBuf::from("/replaced");
        let unchanged = PathBuf::from("/unchanged");
        let unwatched = PathBuf::from("/unwatched");
        let removed = PathBuf::from("/removed");
        let identity = |inode| RootIdentity::Present { device: 1, inode };
        let mut recorded = HashMap::from([
            (replaced.clone(), identity(10)),
            (unchanged.clone(), identity(20)),
            (removed.clone(), identity(40)),
        ]);
        let current = |path: &Path| match path.to_str() {
            Some("/replaced") => identity(11),
            Some("/unchanged") => identity(20),
            _ => RootIdentity::Missing,
        };
        let previous_roots = [replaced.clone(), unchanged, unwatched, removed.clone()];

        assert_eq!(
            take_unreported_root_changes(&previous_roots, &mut recorded, current),
            vec![&replaced, &removed]
        );
        assert_eq!(recorded[&replaced], identity(11));
        assert_eq!(recorded[&removed], RootIdentity::Missing);
        assert!(
            take_unreported_root_changes(&previous_roots, &mut recorded, current).is_empty(),
            "a reported change is not reported again"
        );
    }

    #[test]
    fn delivered_root_change_is_not_reported_again_at_the_swap() {
        let tmpdir = testdir();
        let root = tmpdir.path().join("root");
        std::fs::create_dir(&root).expect("create root");
        let watched_identity = RootIdentity::of(&root);
        assert_ne!(watched_identity, RootIdentity::Missing);
        std::fs::rename(&root, tmpdir.path().join("moved")).expect("rename root");

        let previous_roots = [root.clone()];
        let mut undelivered = HashMap::from([(root.clone(), watched_identity)]);
        assert_eq!(
            take_unreported_root_changes(&previous_roots, &mut undelivered, RootIdentity::of),
            vec![&root],
            "a change no event covered is reported"
        );

        let identities = Arc::new(Mutex::new(HashMap::from([(
            root.clone(),
            watched_identity,
        )])));
        let root_path = root.to_str().expect("utf-8 temp path");
        let events = run_callback_recording_roots(
            recursive_watch(root_path),
            None,
            &[(root_path.as_bytes(), StreamFlags::ROOT_CHANGED.bits(), 0)],
            Arc::new(StreamProgress::new(0, false)),
            identities.clone(),
        );
        assert_eq!(events.len(), 1);
        let mut identities = lock_ignoring_poison(&identities);
        assert_eq!(identities[&root], RootIdentity::Missing);
        assert!(
            take_unreported_root_changes(&previous_roots, &mut identities, RootIdentity::of)
                .is_empty()
        );
    }

    // A rewatch of a root replaced in the meantime must not reset what the
    // swap compares against, or the replacement goes unreported.
    #[test]
    fn swap_reports_a_root_replaced_before_a_rewatch() {
        let tmpdir = testdir();
        let root = tmpdir.path().join("root");
        std::fs::create_dir(&root).expect("create root");
        let (tx, rx) = std::sync::mpsc::channel();
        let mut watcher = FsEventWatcher::new(tx, Config::default()).expect("create watcher");
        watcher
            .append_path(&root, RecursiveMode::Recursive)
            .expect("watch root");

        std::fs::rename(&root, tmpdir.path().join("moved")).expect("rename root");
        std::fs::create_dir(&root).expect("recreate root");
        watcher
            .append_path(&root, RecursiveMode::Recursive)
            .expect("rewatch root");

        let previous_roots = [root.canonicalize().expect("canonical root")];
        watcher.report_root_changes_held_by(&previous_roots);
        let events: Vec<Event> = rx.try_iter().collect::<crate::Result<_>>().expect("events");
        assert_eq!(events.len(), 1, "{events:?}");
        assert_eq!(events[0].kind, EventKind::Remove(RemoveKind::Any));
        assert_eq!(events[0].info(), Some("root changed"));
        assert_eq!(events[0].paths, vec![root]);

        watcher.report_root_changes_held_by(&previous_roots);
        assert!(rx.try_recv().is_err(), "the change is reported once");
    }

    #[test]
    fn test_steam_context_info_send_and_sync() {
        fn check_send<T: Send + Sync>() {}
        check_send::<StreamContextInfo>();
    }

    /// Drives `callback_impl` with the given watch table and raw `(path, flags)` events,
    /// returning everything it delivered. Paths are bytes because FSEvents reports
    /// whatever the filesystem holds, which need not be UTF-8.
    fn run_callback(
        recursive_info: HashMap<PathBuf, WatchInfo>,
        events: &[(&[u8], u32)],
    ) -> Vec<crate::Result<Event>> {
        let events: Vec<_> = events
            .iter()
            .zip(0..)
            .map(|(&(path, flags), event_id)| (path, flags, event_id))
            .collect();
        run_callback_with(
            recursive_info,
            None,
            &events,
            Arc::new(StreamProgress::new(0, false)),
        )
    }

    /// Like `run_callback`, with explicit event ids, a replay filter and the
    /// stream progress the callback records into.
    fn run_callback_with(
        recursive_info: HashMap<PathBuf, WatchInfo>,
        replay: Option<ReplayFilter>,
        events: &[(&[u8], u32, fs::FSEventStreamEventId)],
        progress: Arc<StreamProgress>,
    ) -> Vec<crate::Result<Event>> {
        run_callback_recording_roots(recursive_info, replay, events, progress, Arc::default())
    }

    /// Like `run_callback_with`, recording root identities into `root_identities`.
    fn run_callback_recording_roots(
        recursive_info: HashMap<PathBuf, WatchInfo>,
        replay: Option<ReplayFilter>,
        events: &[(&[u8], u32, fs::FSEventStreamEventId)],
        progress: Arc<StreamProgress>,
        root_identities: Arc<Mutex<HashMap<PathBuf, RootIdentity>>>,
    ) -> Vec<crate::Result<Event>> {
        use std::ffi::CString;
        use std::ptr;

        let (tx, rx) = std::sync::mpsc::channel::<crate::Result<Event>>();
        let event_handler: Arc<Mutex<dyn EventHandler>> = Arc::new(Mutex::new(tx));

        let context = Box::new(StreamContextInfo {
            event_handler,
            recursive_info: Arc::new(recursive_info),
            event_kinds: EventKindMask::ALL,
            progress,
            replay: Mutex::new(replay),
            root_identities,
            stream_number: 0,
        });
        let context_ptr = Box::into_raw(context) as *mut libc::c_void;

        let c_paths: Vec<CString> = events
            .iter()
            .map(|(path, _, _)| CString::new(*path).expect("cstring"))
            .collect();
        let path_ptrs: Vec<_> = c_paths.iter().map(|p| p.as_ptr()).collect();
        let event_paths = NonNull::new(path_ptrs.as_ptr() as *mut libc::c_void).unwrap();

        let flags_arr: Vec<fs::FSEventStreamEventFlags> = events
            .iter()
            .map(|(_, flags, _)| *flags as fs::FSEventStreamEventFlags)
            .collect();
        let event_flags =
            NonNull::new(flags_arr.as_ptr() as *mut fs::FSEventStreamEventFlags).unwrap();

        let ids_arr: Vec<fs::FSEventStreamEventId> =
            events.iter().map(|(_, _, event_id)| *event_id).collect();
        let event_ids = NonNull::new(ids_arr.as_ptr() as *mut fs::FSEventStreamEventId).unwrap();

        let res = std::panic::catch_unwind(|| unsafe {
            callback_impl(
                ptr::null(),
                context_ptr,
                events.len(),
                event_paths,
                event_flags,
                event_ids,
            );
        });
        unsafe {
            drop(Box::from_raw(context_ptr as *mut StreamContextInfo));
        }
        assert!(res.is_ok(), "callback_impl should not panic");

        rx.try_iter().collect()
    }

    #[test]
    fn flush_waits_for_its_own_generation() {
        let mut state = FlushState::new(0, false);

        let first = state.request();
        assert!(!state.is_complete(first), "nothing has been flushed yet");

        // A flush already running when the second request arrives took its
        // generation before that request, so it must not complete it.
        let running = state.pending();
        let second = state.request();
        state.answer(running, 0);
        assert!(state.is_complete(first));
        assert!(!state.is_complete(second));

        let next = state.pending();
        state.answer(next, 0);
        assert!(state.is_complete(second));

        // A late answer from an older flush never moves the counter back.
        state.answer(running, 0);
        assert!(state.is_complete(second));
    }

    // Signals to a runloop source coalesce, so one perform can answer several
    // requests.
    #[test]
    fn one_flush_completes_every_request_made_before_it() {
        let mut state = FlushState::new(0, false);
        let first = state.request();
        let second = state.request();

        let generation = state.pending();
        state.answer(generation, 0);
        assert!(state.is_complete(first));
        assert!(state.is_complete(second));
    }

    // An answered flush is not complete until the callback has handed over
    // the last event the service had queued, which is how an event held for
    // the latency gets through before the stream is stopped.
    #[test]
    fn flush_waits_for_the_queued_events_to_be_delivered() {
        let mut state = FlushState::new(0, false);
        state.record_delivery(10, Instant::now());

        let generation = state.request();
        state.answer(state.pending(), 12);
        assert!(!state.is_complete(generation), "event 12 is still held");

        state.record_delivery(11, Instant::now());
        assert!(!state.is_complete(generation), "event 12 is still held");

        // Zero-id events such as `RootChanged` never move delivery back.
        state.record_delivery(0, Instant::now());
        state.record_delivery(12, Instant::now());
        assert!(state.is_complete(generation));
    }

    #[test]
    fn flush_with_nothing_queued_completes_once_answered() {
        let mut state = FlushState::new(0, false);
        let generation = state.request();
        assert!(!state.is_complete(generation));
        state.answer(state.pending(), 0);
        assert!(state.is_complete(generation));
    }

    #[test]
    fn callback_records_the_highest_delivered_id() {
        let mut recursive_info = HashMap::new();
        recursive_info.insert(
            PathBuf::from("/watched"),
            WatchInfo {
                is_recursive: true,
                reported_path: PathBuf::from("/watched"),
            },
        );
        let progress = Arc::new(StreamProgress::new(0, false));
        // The unwatched path still counts: the service delivered it, so a
        // flush must not wait for it again.
        let events = run_callback_with(
            recursive_info,
            None,
            &[
                (
                    b"/watched/a".as_slice(),
                    StreamFlags::ITEM_CREATED.bits(),
                    0,
                ),
                (
                    b"/elsewhere/b".as_slice(),
                    StreamFlags::ITEM_CREATED.bits(),
                    1,
                ),
            ],
            progress.clone(),
        );
        assert_eq!(events.len(), 1);
        assert_eq!(lock_ignoring_poison(&progress.state).delivered, 1);
    }

    fn recursive_watch(path: &str) -> HashMap<PathBuf, WatchInfo> {
        HashMap::from([(
            PathBuf::from(path),
            WatchInfo {
                is_recursive: true,
                reported_path: PathBuf::from(path),
            },
        )])
    }

    #[test]
    fn replay_resumes_after_the_last_delivery_while_events_may_be_held() {
        assert_eq!(replay_since(500, 900_000, true), Some(500));
        // Idle: only the most recent ids, which an event still on its way from
        // fseventsd would have.
        assert_eq!(
            replay_since(500, 900_000, false),
            Some(900_000 - IDLE_REPLAY_EVENTS)
        );
        assert_eq!(replay_since(899_990, 900_000, false), Some(899_990));
        // Never ahead of the current id, and never from the start of history.
        assert_eq!(replay_since(950_000, 900_000, true), Some(900_000));
        assert_eq!(replay_since(0, 5, true), None);
        assert_eq!(
            replay_since(5, fs::kFSEventStreamEventIdSinceNow, true),
            None
        );
    }

    #[test]
    fn events_may_be_held_only_within_the_hold_window() {
        let window = Duration::from_secs(4);
        let mut state = FlushState::new(7, false);
        let started = state.started_at;
        assert!(state.may_hold_events(started + window, window));
        assert!(!state.may_hold_events(started + window + Duration::from_millis(1), window));

        state.record_delivery(9, started + Duration::from_secs(10));
        assert!(state.may_hold_events(started + Duration::from_secs(13), window));
        assert!(!state.may_hold_events(started + Duration::from_secs(15), window));

        state.history_pending = true;
        assert!(state.may_hold_events(started + Duration::from_secs(60), window));
    }

    fn replay_filter(
        previous_watches: HashMap<PathBuf, WatchInfo>,
        previous_delivered: fs::FSEventStreamEventId,
    ) -> ReplayFilter {
        ReplayFilter {
            since_when: 100,
            swap_event_id: 200,
            previous_watches: Arc::new(previous_watches),
            previous_progress: Arc::new(StreamProgress::new(previous_delivered, false)),
            previous_stream: 1,
        }
    }

    #[test]
    fn replay_filter_keeps_only_what_the_old_stream_still_owed() {
        let filter = replay_filter(recursive_watch("/old"), 150);
        let old = Path::new("/old/file");
        let added = Path::new("/added/file");

        assert_eq!(
            filter.skip(old, 120, 150),
            Some(ReplaySkip::AlreadyDelivered)
        );
        assert_eq!(
            filter.skip(old, 150, 150),
            Some(ReplaySkip::AlreadyDelivered)
        );
        // Held by the old stream when it was stopped.
        assert_eq!(filter.skip(old, 160, 150), None);
        assert_eq!(
            filter.skip(added, 160, 150),
            Some(ReplaySkip::PredatesWatch)
        );
        assert_eq!(filter.skip(added, 201, 150), None);
        // Delivered by the old stream during the overlap, after the swap id.
        assert_eq!(
            filter.skip(old, 230, 240),
            Some(ReplaySkip::AlreadyDelivered)
        );
        assert_eq!(filter.skip(added, 230, 240), None);
        assert_eq!(
            filter.skip(old, 0, 150),
            None,
            "zero-id events are never replayed"
        );
    }

    #[test]
    fn callback_replays_the_held_event_and_skips_the_rest() {
        let mut watches = recursive_watch("/old");
        watches.extend(recursive_watch("/added"));
        let progress = Arc::new(StreamProgress::new(100, true));
        let created = StreamFlags::ITEM_CREATED.bits() | StreamFlags::IS_FILE.bits();
        let events = run_callback_with(
            watches,
            Some(replay_filter(recursive_watch("/old"), 150)),
            &[
                (b"/old/delivered".as_slice(), created, 140),
                (b"/old/held".as_slice(), created, 160),
                (b"/added/before".as_slice(), created, 170),
                (b"/old".as_slice(), StreamFlags::HISTORY_DONE.bits(), 999),
                (
                    b"/old".as_slice(),
                    StreamFlags::ROOT_CHANGED.bits() | StreamFlags::ITEM_REMOVED.bits(),
                    0,
                ),
                (b"/added/after".as_slice(), created, 210),
            ],
            progress.clone(),
        );

        let paths: Vec<_> = events
            .iter()
            .map(|event| event.as_ref().expect("event").paths.clone())
            .collect();
        assert_eq!(
            paths,
            vec![
                vec![PathBuf::from("/old/held")],
                vec![PathBuf::from("/old")],
                vec![PathBuf::from("/added/after")],
            ]
        );
        let state = lock_ignoring_poison(&progress.state);
        assert_eq!(state.delivered, 210, "the HistoryDone id is not an event's");
        assert!(!state.history_pending);
    }

    #[test]
    fn callback_impl_handles_non_utf8_paths_without_panicking() {
        use std::os::unix::ffi::OsStrExt;

        let mut recursive_info = HashMap::new();
        recursive_info.insert(
            PathBuf::from("/tmp"),
            WatchInfo {
                is_recursive: true,
                reported_path: PathBuf::from("/tmp"),
            },
        );

        let bytes = b"/tmp/\xff";
        let events = run_callback(
            recursive_info,
            &[(bytes.as_slice(), StreamFlags::ITEM_CREATED.bits())],
        );

        let event = events
            .first()
            .expect("expected event")
            .as_ref()
            .expect("expected Ok(Event)");
        assert!(
            event.kind.is_create(),
            "expected create event, got {event:?}"
        );
        assert_eq!(event.paths.len(), 1);
        assert_eq!(event.paths[0].as_os_str().as_bytes(), bytes);
    }

    #[test]
    fn callback_impl_ignores_unknown_flag_bits_without_panicking() {
        // Include an unknown bit so the old `from_bits(...).unwrap_or_else(panic!)` behavior
        // would have panicked. New behavior should tolerate it.
        let unknown_mask = !StreamFlags::all().bits();
        let unknown_bit = unknown_mask & unknown_mask.wrapping_neg();
        assert_ne!(unknown_bit, 0, "StreamFlags unexpectedly uses all bits");
        let raw_flag = StreamFlags::ITEM_CREATED.bits() | unknown_bit;
        assert!(
            StreamFlags::from_bits(raw_flag).is_none(),
            "raw_flag must include an unknown bit for this test to be meaningful"
        );

        let mut recursive_info = HashMap::new();
        recursive_info.insert(
            PathBuf::from("/tmp"),
            WatchInfo {
                is_recursive: true,
                reported_path: PathBuf::from("/tmp"),
            },
        );

        let events = run_callback(recursive_info, &[(b"/tmp/file".as_slice(), raw_flag)]);

        let event = events
            .first()
            .expect("expected event")
            .as_ref()
            .expect("expected Ok(Event)");
        assert!(
            event.kind.is_create(),
            "expected create event, got {event:?}"
        );
    }

    #[test]
    fn translate_flags_ignores_is_file_only_events() {
        assert!(translate_flags(StreamFlags::IS_FILE, true).is_empty());
        assert!(
            translate_flags(StreamFlags::IS_FILE | StreamFlags::ITEM_CLONED, true).is_empty(),
            "type-only clone flags should not produce events"
        );
    }

    #[test]
    fn translate_flags_sets_clone_info_for_file_events() {
        let create = translate_flags(
            StreamFlags::ITEM_CREATED | StreamFlags::IS_FILE | StreamFlags::ITEM_CLONED,
            true,
        );
        assert_eq!(create.len(), 1);
        assert_eq!(create[0].kind, EventKind::Create(CreateKind::File));
        assert_eq!(create[0].info(), Some("is: clone"));

        let modify = translate_flags(
            StreamFlags::INODE_META_MOD
                | StreamFlags::ITEM_MODIFIED
                | StreamFlags::IS_FILE
                | StreamFlags::ITEM_CLONED,
            true,
        );
        assert_eq!(modify.len(), 2);
        assert!(
            modify
                .iter()
                .any(|e| matches!(e.kind, EventKind::Modify(ModifyKind::Metadata(_))))
        );
        assert!(
            modify
                .iter()
                .any(|e| matches!(e.kind, EventKind::Modify(ModifyKind::Data(_))))
        );
        assert!(
            modify.iter().all(|e| e.info() == Some("is: clone")),
            "all events should be annotated as clone-related: {modify:?}"
        );
    }

    #[test]
    fn translate_flags_does_not_override_existing_info() {
        let evs = translate_flags(
            StreamFlags::ROOT_CHANGED
                | StreamFlags::ITEM_REMOVED
                | StreamFlags::IS_FILE
                | StreamFlags::ITEM_CLONED,
            true,
        );
        assert_eq!(evs.len(), 1);
        assert_eq!(evs[0].info(), Some("root changed"));
    }

    #[test]
    fn does_not_crash_with_empty_path() {
        let mut watcher = FsEventWatcher::new(|_| {}, Default::default()).unwrap();

        let watch_result = watcher.watch(Path::new(""), RecursiveMode::Recursive);
        assert!(
            matches!(
                watch_result,
                Err(Error {
                    kind: ErrorKind::PathNotFound,
                    paths: _
                })
            ),
            "actual: {watch_result:#?}"
        );

        let unwatch_result = watcher.unwatch(Path::new(""));
        assert!(
            matches!(
                unwatch_result,
                Err(Error {
                    kind: ErrorKind::WatchNotFound,
                    paths: _
                })
            ),
            "actual: {unwatch_result:#?}"
        );
    }

    #[test]
    fn create_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        watcher.watch_recursively(&tmpdir);

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        rx.wait_unordered([expected(path).create_file()]);
    }

    #[test]
    fn write_file() {
        let tmpdir = testdir();

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        let (mut watcher, mut rx) = watcher();

        watcher.watch_recursively(&tmpdir);

        std::fs::write(&path, b"123").expect("write");

        rx.wait_unordered([expected(&path).modify_data_content()]);
    }

    #[test]
    fn chmod_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        let file = std::fs::File::create_new(&path).expect("create");
        let mut permissions = file.metadata().expect("metadata").permissions();
        permissions.set_readonly(true);

        watcher.watch_recursively(&tmpdir);
        file.set_permissions(permissions).expect("set_permissions");

        rx.wait_unordered([expected(&path).modify_meta_owner()]);
    }

    #[test]
    fn rename_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        watcher.watch_recursively(&tmpdir);
        let new_path = tmpdir.path().join("renamed");

        std::fs::rename(&path, &new_path).expect("rename");

        rx.wait_unordered([expected(path).rename_any(), expected(new_path).rename_any()]);
    }

    #[test]
    fn delete_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        let file = tmpdir.path().join("file");
        std::fs::write(&file, "").expect("write");

        watcher.watch_nonrecursively(&tmpdir);

        std::fs::remove_file(&file).expect("remove");

        rx.wait_unordered([expected(&file).remove_file()]);
    }

    #[test]
    fn delete_self_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        let file = tmpdir.path().join("file");
        std::fs::write(&file, "").expect("write");

        watcher.watch_nonrecursively(&file);

        std::fs::remove_file(&file).expect("remove");

        rx.wait_unordered([expected(file).remove_file()]);
    }

    #[test]
    fn delete_self_dir() {
        let tmpdir = testdir();
        let dir = tmpdir.path().join("dir");
        std::fs::create_dir(&dir).expect("create");

        let (mut watcher, mut rx) = watcher();
        watcher.watch_nonrecursively(&dir);

        std::fs::remove_dir(&dir).expect("remove");

        rx.wait_unordered([expected(&dir).remove_folder()]);
    }

    #[test]
    fn create_write_overwrite() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        let overwritten_file = tmpdir.path().join("overwritten_file");
        let overwriting_file = tmpdir.path().join("overwriting_file");
        std::fs::write(&overwritten_file, "123").expect("write1");

        watcher.watch_nonrecursively(&tmpdir);

        std::fs::File::create(&overwriting_file).expect("create");
        std::fs::write(&overwriting_file, "321").expect("write2");
        std::fs::rename(&overwriting_file, &overwritten_file).expect("rename");

        rx.wait_unordered([
            expected(&overwriting_file).create(),
            expected(&overwriting_file).modify_data_content().multiple(),
            expected(&overwriting_file).rename_any(),
            expected(&overwritten_file).rename_any(),
        ]);
    }

    #[test]
    fn create_dir() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        watcher.watch_recursively(&tmpdir);

        let path = tmpdir.path().join("entry");
        std::fs::create_dir(&path).expect("create");

        rx.wait_unordered([expected(&path).create_folder()]);
    }

    #[test]
    fn chmod_dir() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        std::fs::create_dir(&path).expect("create_dir");
        let mut permissions = std::fs::metadata(&path).expect("metadata").permissions();
        permissions.set_readonly(true);

        watcher.watch_recursively(&tmpdir);
        std::fs::set_permissions(&path, permissions).expect("set_permissions");

        rx.wait_unordered([expected(&path).modify_meta_owner()]);
    }

    #[test]
    fn rename_dir() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        let new_path = tmpdir.path().join("new_path");
        std::fs::create_dir(&path).expect("create_dir");

        watcher.watch_recursively(&tmpdir);
        std::fs::rename(&path, &new_path).expect("rename");

        rx.wait_ordered([
            expected(&path).rename_any(),
            expected(&new_path).rename_any(),
        ]);
    }

    #[test]
    fn delete_dir() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        std::fs::create_dir(&path).expect("create_dir");

        watcher.watch_recursively(&tmpdir);
        std::fs::remove_dir(&path).expect("remove");

        rx.wait_unordered([expected(path).remove_folder()]);
    }

    #[test]
    fn rename_dir_twice() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        let new_path = tmpdir.path().join("new_path");
        let new_path2 = tmpdir.path().join("new_path2");
        std::fs::create_dir(&path).expect("create_dir");

        watcher.watch_recursively(&tmpdir);
        std::fs::rename(&path, &new_path).expect("rename");
        std::fs::rename(&new_path, &new_path2).expect("rename2");

        rx.wait_unordered([
            expected(&path).rename_any(),
            expected(&new_path).rename_any(),
            expected(&new_path2).rename_any(),
        ]);
    }

    #[test]
    fn move_out_of_watched_dir() {
        let tmpdir = testdir();
        let subdir = tmpdir.path().join("subdir");
        let (mut watcher, mut rx) = watcher();

        let path = subdir.join("entry");
        std::fs::create_dir_all(&subdir).expect("create_dir_all");
        std::fs::File::create_new(&path).expect("create");

        watcher.watch_recursively(&subdir);
        let new_path = tmpdir.path().join("entry");

        std::fs::rename(&path, &new_path).expect("rename");

        rx.wait_unordered([expected(path).rename_any()]);
    }

    #[test]
    #[ignore = "https://github.com/notify-rs/notify/issues/729"]
    fn create_write_write_rename_write_remove() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let file1 = tmpdir.path().join("entry");
        let file2 = tmpdir.path().join("entry2");
        std::fs::File::create_new(&file2).expect("create file2");
        let new_path = tmpdir.path().join("renamed");

        watcher.watch_recursively(&tmpdir);
        std::fs::write(&file1, "123").expect("write 1");
        std::fs::write(&file2, "321").expect("write 2");
        std::fs::rename(&file1, &new_path).expect("rename");
        std::fs::write(&new_path, b"1").expect("write 3");
        std::fs::remove_file(&new_path).expect("remove");

        rx.wait_ordered([
            expected(&file1).create_file(),
            expected(&file1).modify_data_content(),
            expected(&file2).modify_data_content(),
            expected(&file1).rename_any(),
            expected(&new_path).rename_any(),
            expected(&new_path).modify_data_content(),
            expected(&new_path).remove_file(),
        ]);
    }

    #[test]
    fn rename_twice() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        watcher.watch_recursively(&tmpdir);
        let new_path1 = tmpdir.path().join("renamed1");
        let new_path2 = tmpdir.path().join("renamed2");

        std::fs::rename(&path, &new_path1).expect("rename1");
        std::fs::rename(&new_path1, &new_path2).expect("rename2");

        rx.wait_unordered([
            expected(&path).rename_any(),
            expected(&new_path1).rename_any(),
            expected(&new_path2).rename_any(),
        ]);
    }

    #[test]
    fn set_file_mtime() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        let file = std::fs::File::create_new(&path).expect("create");

        watcher.watch_recursively(&tmpdir);

        file.set_modified(
            std::time::SystemTime::now()
                .checked_sub(Duration::from_secs(60 * 60))
                .expect("time"),
        )
        .expect("set_time");

        rx.wait_unordered([expected(&path).modify_meta_any()]);
    }

    #[test]
    fn write_file_non_recursive_watch() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        watcher.watch_nonrecursively(&path);

        std::fs::write(&path, b"123").expect("write");

        rx.wait_unordered([expected(path).modify_data_content()]);
    }

    #[test]
    fn write_to_a_hardlink_pointed_to_the_watched_file_triggers_an_event() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let subdir = tmpdir.path().join("subdir");
        let file = subdir.join("file");
        let hardlink = tmpdir.path().join("hardlink");

        std::fs::create_dir(&subdir).expect("create");
        std::fs::write(&file, "").expect("file");
        std::fs::hard_link(&file, &hardlink).expect("hardlink");

        watcher.watch_nonrecursively(&file);

        std::fs::write(&hardlink, "123123").expect("write to the hard link");

        rx.wait_unordered([expected(file).modify_data_content()]);
    }

    #[test]
    fn recursive_creation() {
        let tmpdir = testdir();
        let nested1 = tmpdir.path().join("1");
        let nested2 = tmpdir.path().join("1/2");
        let nested3 = tmpdir.path().join("1/2/3");
        let nested4 = tmpdir.path().join("1/2/3/4");
        let nested5 = tmpdir.path().join("1/2/3/4/5");
        let nested6 = tmpdir.path().join("1/2/3/4/5/6");
        let nested7 = tmpdir.path().join("1/2/3/4/5/6/7");
        let nested8 = tmpdir.path().join("1/2/3/4/5/6/7/8");
        let nested9 = tmpdir.path().join("1/2/3/4/5/6/7/8/9");

        let (mut watcher, mut rx) = watcher();

        watcher.watch_recursively(&tmpdir);

        std::fs::create_dir_all(&nested9).expect("create_dir_all");

        rx.wait_ordered([
            expected(&nested1).create_folder(),
            expected(&nested2).create_folder(),
            expected(&nested3).create_folder(),
            expected(&nested4).create_folder(),
            expected(&nested5).create_folder(),
            expected(&nested6).create_folder(),
            expected(&nested7).create_folder(),
            expected(&nested8).create_folder(),
            expected(&nested9).create_folder(),
        ]);
    }

    #[test]
    fn fsevent_watcher_respects_event_kind_mask() {
        use crate::Watcher;
        use notify_types::event::EventKindMask;

        let tmpdir = testdir();
        let (tx, rx) = std::sync::mpsc::channel();

        // Create watcher with CREATE-only mask (no MODIFY events)
        let config = Config::default().with_event_kinds(EventKindMask::CREATE);

        let mut watcher = FsEventWatcher::new(tx, config).expect("create watcher");
        watcher
            .watch(tmpdir.path(), crate::RecursiveMode::Recursive)
            .expect("watch");

        let path = tmpdir.path().join("test_file");

        // Create a file - should generate CREATE event
        std::fs::File::create_new(&path).expect("create");

        // Small delay to let events propagate
        std::thread::sleep(Duration::from_millis(100));

        // Modify the file - should NOT generate event (filtered by mask)
        std::fs::write(&path, "modified content").expect("write modified");

        std::thread::sleep(Duration::from_millis(100));

        // Collect all events
        let events: Vec<_> = rx.try_iter().filter_map(|r| r.ok()).collect();

        // Should have CREATE event
        assert!(
            events.iter().any(|e| e.kind.is_create()),
            "Expected CREATE event, got: {:?}",
            events
        );

        // Should NOT have MODIFY event (filtered out)
        assert!(
            !events.iter().any(|e| e.kind.is_modify()),
            "Should not receive MODIFY events with CREATE-only mask, got: {:?}",
            events
        );
    }

    // Replaces a test that watched 4097 paths to provoke an `FSEventStreamStart` failure
    // (https://github.com/fsnotify/fsevents/issues/48). That path count is exactly what
    // closes fd 0, so the test corrupted the process it ran in and needed a `catch_unwind`
    // around its own cleanup to stay green.
    #[test]
    fn refuses_more_paths_than_fsevents_can_carry() {
        let budget = fsevents_path_budget().expect("path budget");
        if budget > 4096 {
            eprintln!("skipping: RLIMIT_NOFILE leaves a budget of {budget} paths");
            return;
        }

        let tmpdir = testdir();
        let (mut watcher, _rx) = watcher();

        let mut paths = Vec::new();
        for i in 0..=budget {
            let path = tmpdir.path().join(format!("dir_{i}"));
            std::fs::create_dir(&path).expect("create_dir");
            paths.push(PathOp::Watch(
                path,
                WatchPathConfig::new(RecursiveMode::NonRecursive),
            ));
        }

        let err = watcher
            .watcher
            .update_paths(paths)
            .expect_err("watching more paths than the budget must fail");
        assert!(
            matches!(err.source.kind, ErrorKind::MaxFilesWatch),
            "expected MaxFilesWatch, got {err:?}"
        );
    }

    #[test]
    fn path_budget_is_shared_across_live_streams() {
        static ACTIVE_PATHS: AtomicUsize = AtomicUsize::new(0);

        let first = FseventsPathReservation::acquire(&ACTIVE_PATHS, 15, 21)
            .expect("first stream must fit within the budget");
        let active_path_count = FseventsPathReservation::acquire(&ACTIVE_PATHS, 15, 21)
            .expect_err("the combined path count must exceed the budget");
        assert_eq!(active_path_count, 15);

        drop(first);

        let second = FseventsPathReservation::acquire(&ACTIVE_PATHS, 15, 21)
            .expect("stopping the first stream must release its paths");
        drop(second);
        assert_eq!(ACTIVE_PATHS.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn rename_then_remove_remove_event_must_be_the_last_one() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        watcher.watch_recursively(&tmpdir);
        let new_path1 = tmpdir.path().join("renamed1");
        let new_path2 = tmpdir.path().join("renamed2");

        std::fs::rename(&path, &new_path1).expect("rename1");
        std::fs::rename(&new_path1, &new_path2).expect("rename2");

        std::fs::remove_file(&new_path2).expect("remove_file");

        loop {
            let ev = rx.recv();
            if matches!(ev.kind, EventKind::Remove(RemoveKind::File)) {
                assert_eq!(&ev.paths, &[new_path2]);
                break;
            }
        }

        rx.ensure_empty();
    }
}
