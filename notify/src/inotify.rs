//! Inotify watcher implementation for Linux, Android, and FreeBSD 14.5+.
//!
//! The inotify API provides a mechanism for monitoring filesystem events.  Inotify can be used to
//! monitor individual files, or to monitor directories.  When a directory is monitored, inotify
//! will return events for the directory itself, and for files inside the directory.

use super::event::*;
use super::{
    Config, Error, ErrorKind, EventHandler, PathOp, RecursiveMode, Result, StdResult,
    UpdatePathsError, WatchPathConfig, Watcher,
};
use crate::paths::{
    WatchMetadata, WatchPath, absolute_path, is_preserved_watch_root, preserved_watch_mode,
    preserved_watch_roots, recursive_user_watch_ancestor, reported_path,
};
use crate::{BoundSender, Receiver, Sender, bounded, unbounded};
use inotify as inotify_sys;
use inotify_sys::{EventMask, Inotify, WatchDescriptor, WatchMask};
use notify_types::event::EventKindMask;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::ffi::OsStr;
use std::fs::{Metadata, metadata, symlink_metadata};
use std::os::unix::io::AsRawFd;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::thread;
use walkdir::WalkDir;

const INOTIFY: mio::Token = mio::Token(0);
const MESSAGE: mio::Token = mio::Token(1);

/// Flags for a single `inotify_add_watch` call, not event kinds. Never store them in
/// [`Watch::watch_mask`], which is merged into later adds for the same path.
const RESOLUTION_FLAGS: WatchMask = WatchMask::DONT_FOLLOW
    .union(WatchMask::MASK_ADD)
    .union(WatchMask::MASK_CREATE)
    .union(WatchMask::ONLYDIR);

/// Convert an EventKindMask to the corresponding inotify WatchMask.
///
/// When `is_recursive` is true, CREATE and MOVED_TO are always included
/// to enable tracking of newly created subdirectories.
fn event_kind_mask_to_watch_mask(mask: EventKindMask, is_recursive: bool) -> WatchMask {
    let mut watch_mask = WatchMask::empty();

    if is_recursive {
        watch_mask |= WatchMask::CREATE | WatchMask::MOVED_TO;
    }

    if mask.intersects(EventKindMask::CREATE) {
        watch_mask |= WatchMask::CREATE | WatchMask::MOVED_TO;
    }

    if mask.intersects(EventKindMask::REMOVE) {
        watch_mask |= WatchMask::DELETE | WatchMask::MOVED_FROM;
    }

    if mask.intersects(EventKindMask::MODIFY_DATA) {
        // Note: CLOSE_WRITE is intentionally NOT included here because it generates
        // Access(Close(Write)) events, not Modify events. Users who want CLOSE_WRITE
        // events should use ACCESS_CLOSE.
        watch_mask |= WatchMask::MODIFY;
    }

    if mask.intersects(EventKindMask::MODIFY_META) {
        watch_mask |= WatchMask::ATTRIB;
    }

    if mask.intersects(EventKindMask::MODIFY_NAME) {
        watch_mask |= WatchMask::MOVE_SELF;
    }

    if mask.intersects(EventKindMask::ACCESS_OPEN) {
        watch_mask |= WatchMask::OPEN;
    }

    if mask.intersects(EventKindMask::ACCESS_CLOSE) {
        watch_mask |= WatchMask::CLOSE_WRITE;
    }

    if mask.intersects(EventKindMask::ACCESS_CLOSE_NOWRITE) {
        watch_mask |= WatchMask::CLOSE_NOWRITE;
    }

    watch_mask
}

// The EventLoop will set up a mio::Poll and use it to wait for the following:
//
// -  messages telling it what to do
//
// -  events telling it that something has happened on one of the watched files.

struct EventLoop {
    running: bool,
    poll: mio::Poll,
    event_loop_waker: Arc<mio::Waker>,
    event_loop_tx: Sender<EventLoopMsg>,
    event_loop_rx: Receiver<EventLoopMsg>,
    inotify: Option<Inotify>,
    event_handler: Box<dyn EventHandler>,
    /// Absolute path -> inotify descriptor and watch metadata.
    watches: Watches,
    paths: HashMap<WatchDescriptor, PathBuf>,
    rename_event: Option<Event>,
    follow_links: bool,
    event_kind_mask: EventKindMask,
}

struct Watch {
    watch_descriptor: WatchDescriptor,
    watch_mask: WatchMask,
    is_dir: bool,
    dereference: bool,
    metadata: WatchMetadata,
}

/// Absolute path -> [`Watch`], plus how many paths currently hold each descriptor.
///
/// Several paths can share one descriptor (a symlink and the directory a walk reached through it
/// resolve to the same inode), so a descriptor may only be released once its last owner is gone.
/// Keeping the count next to the map makes that check O(1) instead of a scan over every watch,
/// which made tearing down N watches one at a time O(N^2). Mutation goes through `insert`,
/// `remove` and `clear` only, so the count cannot drift; reads go through `Deref`.
#[derive(Default)]
struct Watches {
    by_path: HashMap<PathBuf, Watch>,
    owner_counts: HashMap<WatchDescriptor, usize>,
}

impl Watches {
    fn insert(&mut self, path: PathBuf, watch: Watch) -> Option<Watch> {
        *self
            .owner_counts
            .entry(watch.watch_descriptor.clone())
            .or_insert(0) += 1;
        let previous = self.by_path.insert(path, watch);
        if let Some(previous) = &previous {
            self.release_owner(&previous.watch_descriptor);
        }
        previous
    }

    fn remove(&mut self, path: &Path) -> Option<Watch> {
        let removed = self.by_path.remove(path);
        if let Some(removed) = &removed {
            self.release_owner(&removed.watch_descriptor);
        }
        removed
    }

    fn clear(&mut self) {
        self.by_path.clear();
        self.owner_counts.clear();
    }

    /// Only the metadata is handed out mutably: changing a descriptor in place would bypass the
    /// owner count.
    fn metadata_mut(&mut self, path: &Path) -> Option<&mut WatchMetadata> {
        self.by_path.get_mut(path).map(|watch| &mut watch.metadata)
    }

    fn owner_count(&self, descriptor: &WatchDescriptor) -> usize {
        self.owner_counts.get(descriptor).copied().unwrap_or(0)
    }

    fn release_owner(&mut self, descriptor: &WatchDescriptor) {
        if let Some(count) = self.owner_counts.get_mut(descriptor) {
            *count -= 1;
            if *count == 0 {
                self.owner_counts.remove(descriptor);
            }
        }
    }

    /// Some path other than `except` that holds `descriptor`, if any.
    ///
    /// Scans every watch, so callers consult [`Self::owner_count`] first and only get here when a
    /// descriptor really is shared.
    fn other_owner(&self, descriptor: &WatchDescriptor, except: Option<&Path>) -> Option<PathBuf> {
        self.by_path
            .iter()
            .find(|(path, watch)| {
                except.is_none_or(|except| path.as_path() != except)
                    && &watch.watch_descriptor == descriptor
            })
            .map(|(path, _)| path.clone())
    }
}

impl std::ops::Deref for Watches {
    type Target = HashMap<PathBuf, Watch>;

    fn deref(&self) -> &Self::Target {
        &self.by_path
    }
}

impl<'a> IntoIterator for &'a Watches {
    type Item = (&'a PathBuf, &'a Watch);
    type IntoIter = std::collections::hash_map::Iter<'a, PathBuf, Watch>;

    fn into_iter(self) -> Self::IntoIter {
        self.by_path.iter()
    }
}

/// Watcher implementation based on inotify
#[derive(Debug)]
pub struct INotifyWatcher {
    channel: Sender<EventLoopMsg>,
    waker: Arc<mio::Waker>,
}

/// A batched op with its path already resolved on the caller's thread, as `watch_inner` and
/// `unwatch_inner` do, so a working-directory change while the loop is busy cannot retarget a
/// relative path. The original op is kept for error reporting.
struct ResolvedPathOp {
    op: PathOp,
    target: Result<ResolvedTarget>,
}

enum ResolvedTarget {
    Watch(WatchPath, WatchPathConfig),
    Unwatch(PathBuf),
}

impl ResolvedPathOp {
    fn new(op: PathOp) -> Self {
        let target = match &op {
            PathOp::Watch(path, config) => WatchPath::new(path)
                .map(|watch_path| ResolvedTarget::Watch(watch_path, config.clone())),
            PathOp::Unwatch(path) => absolute_path(path).map(ResolvedTarget::Unwatch),
        };
        Self { op, target }
    }
}

enum EventLoopMsg {
    AddWatch(WatchPath, WatchPathConfig, Sender<Result<()>>),
    RemoveWatch(PathBuf, Sender<Result<()>>),
    /// A whole [`Watcher::update_paths`] batch, applied in one visit to the loop.
    UpdatePaths(Vec<ResolvedPathOp>, Sender<StdResult<(), UpdatePathsError>>),
    GetWatchedPaths(Sender<Vec<(PathBuf, RecursiveMode)>>),
    Shutdown,
    Configure(Config, BoundSender<Result<bool>>),
}

#[inline]
fn watch_metadata(path: &Path, dereference: bool) -> std::io::Result<Metadata> {
    if dereference {
        metadata(path)
    } else {
        symlink_metadata(path)
    }
}

#[inline]
fn add_watch_by_event(
    path: &PathBuf,
    event: &inotify_sys::Event<&OsStr>,
    watches: &HashMap<PathBuf, Watch>,
    add_watches: &mut Vec<WatchPath>,
) {
    if event.mask.contains(EventMask::ISDIR) {
        if let Some(parent_path) = path.parent() {
            if let Some(watch) = watches.get(parent_path) {
                if watch.metadata.is_recursive {
                    add_watches.push(WatchPath::from_parts(
                        path.to_owned(),
                        reported_path(parent_path, &watch.metadata.reported_path, path),
                    ));
                }
            }
        }
    }
}

/// Queue `path` for removal, if it is watched and `descriptor` still matches its watch.
#[inline]
fn queue_watch_removal(
    path: &Path,
    descriptor: Option<&WatchDescriptor>,
    watches: &HashMap<PathBuf, Watch>,
    remove_watches: &mut BTreeMap<PathBuf, WatchRemoval>,
    removal: WatchRemoval,
) {
    let watched = watches
        .get(path)
        .is_some_and(|watch| descriptor.is_none_or(|wd| &watch.watch_descriptor == wd));
    if watched {
        let pending = remove_watches.entry(path.to_owned()).or_insert(removal);
        *pending = (*pending).max(removal);
    }
}

/// Variant order is load-bearing: coalescing keeps the greater of two pending removals.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum WatchRemoval {
    /// The watch may still be installed, so remove it from inotify as well as local state.
    WithOsCall,
    /// The kernel removed the event's root descriptor, but descendant descriptors may still be
    /// installed if their filesystem objects survived, for example after being moved elsewhere.
    DescriptorAlreadyRemoved,
}

#[inline]
fn unmount_event(path: PathBuf) -> Event {
    Event::new(EventKind::Remove(RemoveKind::Other))
        .add_path(path)
        .set_info("unmount")
}

impl EventLoop {
    pub fn new(
        inotify: Inotify,
        event_handler: Box<dyn EventHandler>,
        config: &Config,
    ) -> Result<Self> {
        let (event_loop_tx, event_loop_rx) = unbounded::<EventLoopMsg>();
        let poll = mio::Poll::new()?;

        let event_loop_waker = Arc::new(mio::Waker::new(poll.registry(), MESSAGE)?);

        let inotify_fd = inotify.as_raw_fd();
        let mut evented_inotify = mio::unix::SourceFd(&inotify_fd);
        poll.registry()
            .register(&mut evented_inotify, INOTIFY, mio::Interest::READABLE)?;

        let event_loop = EventLoop {
            running: true,
            poll,
            event_loop_waker,
            event_loop_tx,
            event_loop_rx,
            inotify: Some(inotify),
            event_handler,
            watches: Watches::default(),
            paths: HashMap::new(),
            rename_event: None,
            follow_links: config.follow_symlinks(),
            event_kind_mask: config.event_kinds(),
        };
        Ok(event_loop)
    }

    // Run the event loop.
    pub fn run(self) {
        let _ = thread::Builder::new()
            .name("notify-rs inotify loop".to_string())
            .spawn(|| self.event_loop_thread());
    }

    fn event_loop_thread(mut self) {
        let mut events = mio::Events::with_capacity(16);
        loop {
            // Wait for something to happen.
            match self.poll.poll(&mut events, None) {
                Err(ref e) if matches!(e.kind(), std::io::ErrorKind::Interrupted) => {
                    // System call was interrupted, we will retry
                    // TODO: Not covered by tests (to reproduce likely need to setup signal handlers)
                }
                Err(e) => panic!("poll failed: {e}"),
                Ok(()) => {}
            }

            // Process whatever happened.
            for event in &events {
                self.handle_event(event);
            }

            // Stop, if we're done.
            if !self.running {
                break;
            }
        }
    }

    // Handle a single event.
    fn handle_event(&mut self, event: &mio::event::Event) {
        match event.token() {
            MESSAGE => {
                // The channel is readable - handle messages.
                self.handle_messages()
            }
            INOTIFY => {
                // inotify has something to tell us.
                self.handle_inotify()
            }
            _ => unreachable!(),
        }
    }

    fn handle_messages(&mut self) {
        while let Ok(msg) = self.event_loop_rx.try_recv() {
            match msg {
                EventLoopMsg::AddWatch(path, config, tx) => {
                    let _ = tx.send(self.add_watch(path, config, true));
                }
                EventLoopMsg::RemoveWatch(path, tx) => {
                    let _ = tx.send(self.remove_watch(path, false));
                }
                EventLoopMsg::UpdatePaths(ops, tx) => {
                    let _ = tx.send(self.update_paths(ops));
                }
                EventLoopMsg::GetWatchedPaths(tx) => {
                    let _ = tx.send(
                        self.watches
                            .iter()
                            .filter(|(_path, watch)| watch.metadata.is_user_watch)
                            .map(|(_path, watch)| {
                                (
                                    watch.metadata.reported_path.clone(),
                                    if watch.metadata.user_is_recursive {
                                        RecursiveMode::Recursive
                                    } else {
                                        RecursiveMode::NonRecursive
                                    },
                                )
                            })
                            .collect(),
                    );
                }
                EventLoopMsg::Shutdown => {
                    let _ = self.remove_all_watches();
                    if let Some(inotify) = self.inotify.take() {
                        let _ = inotify.close();
                    }
                    self.running = false;
                    break;
                }
                EventLoopMsg::Configure(config, tx) => {
                    self.configure_raw_mode(config, tx);
                }
            }
        }
    }

    /// Applies each operation exactly as `AddWatch`/`RemoveWatch` would, in order, stopping at the
    /// first failure. Sharing [`crate::update_paths`] with the trait's default keeps the error
    /// contract identical: the failed op is `origin`, the unattempted ones are `remaining`.
    fn update_paths(&mut self, ops: Vec<ResolvedPathOp>) -> StdResult<(), UpdatePathsError> {
        let mut ops = ops.into_iter();
        while let Some(ResolvedPathOp { op, target }) = ops.next() {
            let applied = target.and_then(|target| match target {
                ResolvedTarget::Watch(watch_path, config) => {
                    self.add_watch(watch_path, config, true)
                }
                ResolvedTarget::Unwatch(absolute) => self.remove_watch(absolute, false),
            });
            if let Err(source) = applied {
                return Err(UpdatePathsError {
                    source,
                    origin: Some(op),
                    remaining: ops.map(|remaining| remaining.op).collect(),
                });
            }
        }
        Ok(())
    }

    fn configure_raw_mode(&mut self, _config: Config, tx: BoundSender<Result<bool>>) {
        tx.send(Ok(false))
            .expect("configuration channel disconnected");
    }

    fn handle_inotify(&mut self) {
        let mut add_watches = Vec::new();
        let mut remove_watches = BTreeMap::new();

        if let Some(ref mut inotify) = self.inotify {
            let mut buffer = [0; 1024];
            // Read all buffers available.
            loop {
                match inotify.read_events(&mut buffer) {
                    Ok(events) => {
                        let mut num_events = 0;
                        for event in events {
                            log::trace!("inotify event: {event:?}");

                            num_events += 1;
                            if event.mask.contains(EventMask::Q_OVERFLOW) {
                                let ev = Ok(Event::new(EventKind::Other).set_flag(Flag::Rescan));
                                self.event_handler.handle_event(ev);
                            }

                            if event.mask.contains(EventMask::IGNORED) {
                                // The kernel sends IGNORED whenever it removes a descriptor,
                                // regardless of the configured mask. A replacement watch may
                                // already occupy the same pathname, hence the descriptor check.
                                if let Some(path) = self.paths.get(&event.wd).cloned() {
                                    if self
                                        .watches
                                        .get(&path)
                                        .is_some_and(|watch| watch.watch_descriptor == event.wd)
                                    {
                                        queue_watch_removal(
                                            &path,
                                            None,
                                            &self.watches,
                                            &mut remove_watches,
                                            WatchRemoval::DescriptorAlreadyRemoved,
                                        );
                                    } else {
                                        self.paths.remove(&event.wd);
                                    }
                                }
                                continue;
                            }

                            let paths = self.paths.get(&event.wd).and_then(|root| {
                                self.watches.get(root).map(|watch| match event.name {
                                    Some(name) => {
                                        let path = root.join(name);
                                        let reported_path = reported_path(
                                            root,
                                            &watch.metadata.reported_path,
                                            &path,
                                        );
                                        (path, reported_path)
                                    }
                                    None => (root.clone(), watch.metadata.reported_path.clone()),
                                })
                            });

                            let (path, event_path) = match paths {
                                Some(paths) => paths,
                                None => {
                                    log::debug!("inotify event with unknown descriptor: {event:?}");
                                    continue;
                                }
                            };

                            let mut evs = Vec::new();

                            if event.mask.contains(EventMask::MOVED_FROM) {
                                queue_watch_removal(
                                    &path,
                                    None,
                                    &self.watches,
                                    &mut remove_watches,
                                    WatchRemoval::WithOsCall,
                                );

                                let event = Event::new(EventKind::Modify(ModifyKind::Name(
                                    RenameMode::From,
                                )))
                                .add_path(event_path.clone())
                                .set_tracker(event.cookie as usize);

                                self.rename_event = Some(event.clone());

                                evs.push(event);
                            } else if event.mask.contains(EventMask::MOVED_TO) {
                                evs.push(
                                    Event::new(EventKind::Modify(ModifyKind::Name(RenameMode::To)))
                                        .set_tracker(event.cookie as usize)
                                        .add_path(event_path.clone()),
                                );

                                let trackers_match =
                                    self.rename_event.as_ref().and_then(|e| e.tracker())
                                        == Some(event.cookie as usize);

                                if trackers_match {
                                    let rename_event = self.rename_event.take().unwrap(); // unwrap is safe because `rename_event` must be set at this point
                                    evs.push(
                                        Event::new(EventKind::Modify(ModifyKind::Name(
                                            RenameMode::Both,
                                        )))
                                        .set_tracker(event.cookie as usize)
                                        .add_some_path(rename_event.paths.first().cloned())
                                        .add_path(event_path.clone()),
                                    );
                                }
                                add_watch_by_event(&path, &event, &self.watches, &mut add_watches);
                            }
                            if event.mask.contains(EventMask::MOVE_SELF) {
                                evs.push(
                                    Event::new(EventKind::Modify(ModifyKind::Name(
                                        RenameMode::From,
                                    )))
                                    .add_path(event_path.clone()),
                                );
                                // TODO stat the path and get to new path
                                // - emit To and Both events
                                // - change prefix for further events
                            }
                            if event.mask.contains(EventMask::CREATE) {
                                evs.push(
                                    Event::new(EventKind::Create(
                                        if event.mask.contains(EventMask::ISDIR) {
                                            CreateKind::Folder
                                        } else {
                                            CreateKind::File
                                        },
                                    ))
                                    .add_path(event_path.clone()),
                                );
                                add_watch_by_event(&path, &event, &self.watches, &mut add_watches);
                            }
                            if event.mask.contains(EventMask::DELETE) {
                                evs.push(
                                    Event::new(EventKind::Remove(
                                        if event.mask.contains(EventMask::ISDIR) {
                                            RemoveKind::Folder
                                        } else {
                                            RemoveKind::File
                                        },
                                    ))
                                    .add_path(event_path.clone()),
                                );
                                queue_watch_removal(
                                    &path,
                                    None,
                                    &self.watches,
                                    &mut remove_watches,
                                    WatchRemoval::WithOsCall,
                                );
                            }
                            if event.mask.contains(EventMask::DELETE_SELF) {
                                let remove_kind = match self.watches.get(&path) {
                                    Some(watch) if watch.is_dir => RemoveKind::Folder,
                                    Some(_) => RemoveKind::File,
                                    None => RemoveKind::Other,
                                };
                                evs.push(
                                    Event::new(EventKind::Remove(remove_kind))
                                        .add_path(event_path.clone()),
                                );
                                // Deleting a watched inode removes its watch in the kernel and
                                // queues IGNORED, so calling inotify_rm_watch would return EINVAL.
                                queue_watch_removal(
                                    &path,
                                    Some(&event.wd),
                                    &self.watches,
                                    &mut remove_watches,
                                    WatchRemoval::DescriptorAlreadyRemoved,
                                );
                            }
                            if event.mask.contains(EventMask::UNMOUNT) {
                                evs.push(unmount_event(event_path.clone()));
                                // The kernel has already removed this watch descriptor and will
                                // emit IGNORED; clean up internal state without inotify_rm_watch.
                                // ref. https://www.man7.org/linux/man-pages/man7/inotify.7.html
                                queue_watch_removal(
                                    &path,
                                    Some(&event.wd),
                                    &self.watches,
                                    &mut remove_watches,
                                    WatchRemoval::DescriptorAlreadyRemoved,
                                );
                            }
                            if event.mask.contains(EventMask::MODIFY) {
                                evs.push(
                                    Event::new(EventKind::Modify(ModifyKind::Data(
                                        DataChange::Any,
                                    )))
                                    .add_path(event_path.clone()),
                                );
                            }
                            if event.mask.contains(EventMask::CLOSE_WRITE) {
                                evs.push(
                                    Event::new(EventKind::Access(AccessKind::Close(
                                        AccessMode::Write,
                                    )))
                                    .add_path(event_path.clone()),
                                );
                            }
                            if event.mask.contains(EventMask::CLOSE_NOWRITE) {
                                evs.push(
                                    Event::new(EventKind::Access(AccessKind::Close(
                                        AccessMode::Read,
                                    )))
                                    .add_path(event_path.clone()),
                                );
                            }
                            if event.mask.contains(EventMask::ATTRIB) {
                                evs.push(
                                    Event::new(EventKind::Modify(ModifyKind::Metadata(
                                        MetadataKind::Any,
                                    )))
                                    .add_path(event_path.clone()),
                                );
                            }
                            if event.mask.contains(EventMask::OPEN) {
                                evs.push(
                                    Event::new(EventKind::Access(AccessKind::Open(
                                        AccessMode::Any,
                                    )))
                                    .add_path(event_path.clone()),
                                );
                            }

                            // Filter events based on EventKindMask before delivery
                            for ev in evs {
                                if self.event_kind_mask.matches(&ev.kind) {
                                    self.event_handler.handle_event(Ok(ev));
                                }
                            }
                        }

                        // All events read. Break out.
                        if num_events == 0 {
                            break;
                        }
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        // No events read. Break out.
                        break;
                    }
                    Err(e) => {
                        self.event_handler.handle_event(Err(Error::io(e)));
                    }
                }
            }
        }

        // An ancestor sorts before its descendants, so reverse order removes descendants first:
        // recursive ancestor cleanup then neither repeats syscalls for kernel-removed watches nor
        // drops the mapping for a live, moved-out descendant.
        for (path, removal) in remove_watches.into_iter().rev() {
            if !self.watches.contains_key(&path) {
                continue;
            }

            let result = match removal {
                WatchRemoval::WithOsCall => self.remove_watch(path, true),
                WatchRemoval::DescriptorAlreadyRemoved => {
                    self.remove_watch_without_root_os_call(path, true)
                }
            };
            if let Err(err) = result {
                log::warn!("Unable to remove the path from the watches: {err:?}");
            }
        }

        for path in add_watches {
            let config = WatchPathConfig::new(RecursiveMode::Recursive);
            if let Err(add_watch_error) = self.add_watch(path, config, false) {
                // The handler should be notified if we have reached the limit.
                // Otherwise, the user might expect that a recursive watch
                // is continuing to work correctly, but it's not.
                if let ErrorKind::MaxFilesWatch = add_watch_error.kind {
                    self.event_handler.handle_event(Err(add_watch_error));

                    // After that kind of a error we should stop adding watches,
                    // because the limit has already reached and all next calls
                    // will return us only the same error.
                    break;
                }
            }
        }
    }

    fn add_watch(
        &mut self,
        path: WatchPath,
        config: WatchPathConfig,
        watch_self: bool,
    ) -> Result<()> {
        let is_recursive = config.recursive_mode().is_recursive();
        // a recursive watch has to resolve the path before it can walk it
        let dereference = config.dereference_symlinks() || is_recursive;
        let path_is_dir = watch_metadata(&path.absolute, dereference)
            .map_err(Error::io_watch)?
            .is_dir();
        let requested_is_recursive = is_recursive && path_is_dir;
        if watch_self {
            if let Some(watch) = self
                .watches
                .get(&path.absolute)
                .filter(|watch| watch.metadata.is_user_watch)
            {
                if watch.metadata.user_is_recursive == requested_is_recursive
                    && watch.metadata.reported_path == path.requested
                    && watch.dereference == dereference
                {
                    return Ok(());
                }

                // Rewatching an explicit user watch replaces its requested mode and reported path
                // instead of merging with the previous metadata. If the current entry also carries
                // recursive coverage from an ancestor, remember that ancestor before removal so we
                // can rebuild that inherited coverage below.
                let inherited_recursive_root =
                    if !requested_is_recursive && path_is_dir && watch.metadata.is_recursive {
                        recursive_user_watch_ancestor(
                            &path.absolute,
                            self.watches
                                .iter()
                                .map(|(path, watch)| (path, &watch.metadata)),
                        )
                    } else {
                        None
                    };
                let replaced_path = path.absolute.clone();
                self.remove_watch(replaced_path.clone(), false)?;

                if let Some((ancestor_path, ancestor_reported_path)) = inherited_recursive_root {
                    // Removing a directory watch removes its recursively inherited children too.
                    // Re-add them as non-user watches so the ancestor recursive watch still covers
                    // this subtree after the user watch is replaced.
                    let entries = recursive_directory_paths(
                        replaced_path.clone(),
                        self.follow_links,
                        self.recursive_walk_barriers(),
                    )
                    .map(|entry| {
                        let absolute = entry;
                        let requested =
                            reported_path(&ancestor_path, &ancestor_reported_path, &absolute);
                        WatchPath::from_parts(absolute, requested)
                    });
                    self.add_watches_for_paths(entries, true, true, false)?;
                }
            } else if self.watches.get(&path.absolute).is_some_and(|watch| {
                !dereference && !path_is_dir && watch.is_dir && watch.metadata.is_recursive
            }) {
                // A recursive walk already followed this link. Remove its inherited subtree before
                // replacing the root with an explicit watch on the link itself.
                self.remove_watch(path.absolute.clone(), false)?;
            }
        }

        // If the watch is not recursive, or if we determine (by stat'ing the path to get its
        // metadata) that the watched path is not a directory, add a single path watch.
        if !requested_is_recursive {
            return self.add_single_watch(path, false, dereference, true, path_is_dir);
        }

        let root = path.clone();
        let entries = recursive_directory_paths(
            root.absolute.clone(),
            self.follow_links,
            self.recursive_walk_barriers(),
        )
        .map(move |entry| root.child(entry));

        self.add_watches_for_paths(entries, is_recursive, dereference, watch_self)
    }

    fn recursive_walk_barriers(&self) -> HashSet<PathBuf> {
        self.watches
            .iter()
            .filter(|(_, watch)| {
                watch.metadata.is_user_watch && !watch.dereference && !watch.is_dir
            })
            .map(|(path, _)| path.clone())
            .collect()
    }

    /// Every path must be a directory once resolved: callers pass the output of
    /// `recursive_directory_paths`, which yields only directories, so the watch records
    /// `is_dir` without a stat of its own.
    fn add_watches_for_paths<I>(
        &mut self,
        paths: I,
        is_recursive: bool,
        dereference: bool,
        mut watch_self: bool,
    ) -> Result<()>
    where
        I: IntoIterator<Item = WatchPath>,
    {
        for path in paths {
            // entries below the root were reached by following links, so they observe what they
            // resolved to
            let entry_dereference = if watch_self { dereference } else { true };
            match self.add_single_watch(path, is_recursive, entry_dereference, watch_self, true) {
                Ok(()) => {}
                // TOCTOU: a subdirectory can disappear between walkdir listing it and us adding an
                // inotify watch for it. This should not fail the overall recursive watch call.
                Err(err) if !watch_self && matches!(err.kind, ErrorKind::PathNotFound) => {}
                Err(err) => return Err(err),
            }
            watch_self = false;
        }

        Ok(())
    }

    fn add_single_watch(
        &mut self,
        path: WatchPath,
        is_recursive: bool,
        requested_dereference: bool,
        watch_self: bool,
        is_dir: bool,
    ) -> Result<()> {
        // Build watch mask from configured event kinds for kernel-level filtering
        let mut watchmask = event_kind_mask_to_watch_mask(self.event_kind_mask, is_recursive);

        if watch_self {
            watchmask.insert(WatchMask::DELETE_SELF);
            watchmask.insert(WatchMask::MOVE_SELF);
        }

        let existing_watch = self.watches.get(&path.absolute);
        // an explicit watch decides for its own path, a walk must not overrule it #255
        let dereference = if watch_self {
            requested_dereference
        } else {
            existing_watch
                .filter(|watch| watch.metadata.is_user_watch)
                .map_or(requested_dereference, |watch| watch.dereference)
        };
        let previous_descriptor = existing_watch.map(|watch| watch.watch_descriptor.clone());

        let mut add_mask = watchmask;
        if let Some(watch) = existing_watch {
            watchmask.insert(watch.watch_mask);
            add_mask = watchmask | WatchMask::MASK_ADD;
        }
        if !dereference {
            add_mask.insert(WatchMask::DONT_FOLLOW);
        }
        // the kernel then refuses a path that stopped being a directory since the caller's
        // stat, so a recorded `is_dir` of true always holds for the inode actually watched
        if is_dir {
            add_mask.insert(WatchMask::ONLYDIR);
        }

        if let Some(ref mut inotify) = self.inotify {
            log::trace!("adding inotify watch: {}", path.absolute.display());

            match inotify.watches().add(&path.absolute, add_mask) {
                // retrying as a non-directory never takes this arm again, and its post-add
                // stat records whatever type the path has by then
                Err(e) if is_dir && e.raw_os_error() == Some(libc::ENOTDIR) => self
                    .add_single_watch(path, is_recursive, requested_dereference, watch_self, false),
                Err(e) => {
                    Err(if e.raw_os_error() == Some(libc::ENOSPC) {
                        // do not report inotify limits as "no more space" on linux #266
                        Error::new(ErrorKind::MaxFilesWatch)
                    } else if e.kind() == std::io::ErrorKind::NotFound {
                        Error::new(ErrorKind::PathNotFound)
                    } else {
                        Error::io(e)
                    }
                    .add_path(path.requested))
                }
                Ok(w) => {
                    debug_assert!(!watchmask.intersects(RESOLUTION_FLAGS));
                    // inotify has no inverse of ONLYDIR, so a path the caller saw as a file
                    // is checked again in case a directory replaced it before the add
                    let is_dir = if is_dir {
                        true
                    } else {
                        match watch_metadata(&path.absolute, dereference) {
                            Ok(metadata) => metadata.is_dir(),
                            Err(e) => {
                                // Avoid leaking an inotify watch if we can't stat after adding it.
                                // This can happen due to racy deletions.
                                let _ = inotify.watches().remove(w.clone());
                                return Err(Error::io_watch(e).add_path(path.requested));
                            }
                        }
                    };
                    let metadata = if let Some(existing_watch) = existing_watch {
                        WatchMetadata::new(
                            &path,
                            is_recursive,
                            watch_self,
                            Some(&existing_watch.metadata),
                            self.watches
                                .iter()
                                .map(|(path, watch)| (path, &watch.metadata)),
                        )
                    } else {
                        WatchMetadata {
                            is_recursive,
                            reported_path: path.requested.clone(),
                            is_user_watch: watch_self,
                            user_is_recursive: watch_self && is_recursive,
                        }
                    };

                    // re-resolving a path can land on a different inode, so release the old
                    // descriptor or it keeps reporting under this path
                    if let Some(previous) = previous_descriptor.filter(|previous| *previous != w) {
                        // a walk that followed the link shares this descriptor #255
                        // `path.absolute` itself is one of the owners counted here.
                        let still_watched = if self.watches.owner_count(&previous) > 1 {
                            self.watches
                                .other_owner(&previous, Some(path.absolute.as_path()))
                        } else {
                            None
                        };
                        match still_watched {
                            Some(other) => {
                                self.paths.insert(previous, other);
                            }
                            None => {
                                self.paths.remove(&previous);
                                Self::remove_single_descriptor(&mut inotify.watches(), previous);
                            }
                        }
                    }

                    self.watches.insert(
                        path.absolute.clone(),
                        Watch {
                            watch_descriptor: w.clone(),
                            watch_mask: watchmask,
                            is_dir,
                            dereference,
                            metadata,
                        },
                    );
                    self.paths.insert(w, path.absolute);
                    Ok(())
                }
            }
        } else {
            Ok(())
        }
    }

    fn remove_watch(&mut self, path: PathBuf, remove_recursive: bool) -> Result<()> {
        let watch = self
            .watches
            .remove(&path)
            .ok_or_else(|| Error::watch_not_found().add_path(path.clone()))?;
        log::trace!("removing inotify watch for {path:?}, remove_recursive: {remove_recursive:?}");

        let mut removed_descriptors = vec![watch.watch_descriptor];
        if watch.metadata.is_recursive || remove_recursive {
            // Computed here, after `path` left the map, because only this branch reads it and it
            // is a scan over every watch. The result is the same as computing it up front: the
            // scan already excludes `path` itself, and nothing else has changed yet.
            let preserved_roots = preserved_watch_roots(
                &path,
                remove_recursive,
                self.watches
                    .iter()
                    .map(|(path, watch)| (path, &watch.metadata)),
            );
            let mut remove_list = Vec::new();
            let mut reset_list = Vec::new();
            for candidate in self.watches.keys() {
                if candidate.starts_with(&path) {
                    if let Some(user_is_recursive) =
                        preserved_watch_mode(candidate, &preserved_roots)
                    {
                        if !user_is_recursive
                            || is_preserved_watch_root(candidate, &preserved_roots)
                        {
                            reset_list.push(candidate.clone());
                        }
                        continue;
                    }

                    remove_list.push(candidate.clone());
                }
            }

            for path in remove_list {
                if let Some(watch) = self.watches.remove(&path) {
                    removed_descriptors.push(watch.watch_descriptor);
                }
            }
            for path in reset_list {
                if let Some(metadata) = self.watches.metadata_mut(&path) {
                    metadata.is_recursive = metadata.user_is_recursive;
                }
            }
        }

        self.release_descriptors(removed_descriptors);
        Ok(())
    }

    /// Remove descriptors that no remaining logical path uses, and repoint shared descriptors.
    fn release_descriptors<I>(&mut self, descriptors: I)
    where
        I: IntoIterator<Item = WatchDescriptor>,
    {
        let descriptors: HashSet<_> = descriptors.into_iter().collect();
        for descriptor in descriptors {
            if self.watches.owner_count(&descriptor) > 0 {
                // Still shared: keep the reverse mapping if it already names a remaining owner,
                // otherwise repoint it at one. Any remaining owner is acceptable, as before.
                let mapped_to_owner = self.paths.get(&descriptor).is_some_and(|path| {
                    self.watches
                        .get(path)
                        .is_some_and(|watch| watch.watch_descriptor == descriptor)
                });
                if !mapped_to_owner {
                    if let Some(path) = self.watches.other_owner(&descriptor, None) {
                        self.paths.insert(descriptor, path);
                    }
                }
                continue;
            }

            self.paths.remove(&descriptor);
            if let Some(ref mut inotify) = self.inotify {
                Self::remove_single_descriptor(&mut inotify.watches(), descriptor);
            }
        }
    }

    /// Remove a root watch after the kernel has already invalidated its descriptor.
    ///
    /// Only the root skips `inotify_rm_watch`. Recursive descendants are removed individually
    /// because their filesystem objects—and therefore their descriptors—may still be live.
    fn remove_watch_without_root_os_call(
        &mut self,
        path: PathBuf,
        remove_recursive: bool,
    ) -> Result<()> {
        match self.watches.remove(&path) {
            None => return Err(Error::watch_not_found().add_path(path)),
            Some(watch) => {
                self.paths.remove(&watch.watch_descriptor);

                if watch.metadata.is_recursive || remove_recursive {
                    // Lazily, as in `remove_watch`: the scan excludes `path` itself, so computing
                    // it after the removal gives the same roots.
                    let preserved_roots = preserved_watch_roots(
                        &path,
                        remove_recursive,
                        self.watches
                            .iter()
                            .map(|(path, watch)| (path, &watch.metadata)),
                    );
                    let mut inotify_watches =
                        self.inotify.as_mut().map(|inotify| inotify.watches());
                    let mut remove_list = Vec::new();
                    let mut reset_list = Vec::new();
                    for (w, p) in &self.paths {
                        if p.starts_with(&path) {
                            if let Some(user_is_recursive) =
                                preserved_watch_mode(p, &preserved_roots)
                            {
                                if !user_is_recursive
                                    || is_preserved_watch_root(p, &preserved_roots)
                                {
                                    reset_list.push(p.clone());
                                }
                                continue;
                            }

                            // The kernel removing the root does not prove that this descendant's
                            // descriptor was removed, for example if it was moved elsewhere.
                            if let Some(inotify_watches) = inotify_watches.as_mut() {
                                Self::remove_single_descriptor(inotify_watches, w.clone());
                            }
                            self.watches.remove(p);
                            remove_list.push(w.clone());
                        }
                    }
                    for w in remove_list {
                        self.paths.remove(&w);
                    }
                    for p in reset_list {
                        if let Some(metadata) = self.watches.metadata_mut(&p) {
                            metadata.is_recursive = metadata.user_is_recursive;
                        }
                    }
                }
            }
        }

        Ok(())
    }

    /// Remove a descriptor while tolerating the deletion race documented by inotify.
    ///
    /// Linux may invalidate a watch before its queued deletion event is handled. In that case
    /// `inotify_rm_watch` returns EINVAL, but the requested end state has already been reached.
    /// Other errors indicate an unexpected descriptor or inotify-instance failure and stay visible.
    fn remove_single_descriptor(watches: &mut inotify::Watches, wd: WatchDescriptor) {
        if let Err(err) = watches.remove(wd) {
            if err.raw_os_error() == Some(libc::EINVAL) {
                log::trace!("watch descriptor was already removed from inotify: {err:?}");
            } else {
                log::warn!("unable to remove watch descriptor from inotify: {err:?}");
            }
        }
    }

    fn remove_all_watches(&mut self) -> Result<()> {
        if let Some(ref mut inotify) = self.inotify {
            let mut inotify_watches = inotify.watches();
            for (w, p) in &self.paths {
                inotify_watches
                    .remove(w.clone())
                    .map_err(|e| Error::io(e).add_path(p.into()))?;
            }
            self.watches.clear();
            self.paths.clear();
        }
        Ok(())
    }
}

/// return `DirEntry` when it is a directory
fn filter_dir(e: walkdir::Result<walkdir::DirEntry>) -> Option<walkdir::DirEntry> {
    if let Ok(e) = e {
        if e.file_type().is_dir() {
            return Some(e);
        }
    }
    None
}

fn recursive_directory_paths(
    root: PathBuf,
    follow_links: bool,
    barriers: HashSet<PathBuf>,
) -> impl Iterator<Item = PathBuf> {
    WalkDir::new(root)
        .follow_links(follow_links)
        .into_iter()
        .filter_entry(move |entry| !barriers.contains(entry.path()))
        .filter_map(filter_dir)
        .map(|entry| entry.into_path())
}

impl INotifyWatcher {
    fn from_event_handler(event_handler: Box<dyn EventHandler>, config: &Config) -> Result<Self> {
        let inotify = Inotify::init()?;
        let event_loop = EventLoop::new(inotify, event_handler, config)?;
        let channel = event_loop.event_loop_tx.clone();
        let waker = event_loop.event_loop_waker.clone();
        event_loop.run();
        Ok(INotifyWatcher { channel, waker })
    }

    fn watch_inner(&mut self, path: &Path, config: WatchPathConfig) -> Result<()> {
        let pb = WatchPath::new(path)?;
        let (tx, rx) = unbounded();
        let msg = EventLoopMsg::AddWatch(pb, config, tx);

        self.channel.send(msg)?;
        self.waker.wake()?;
        rx.recv().map_err(Error::from)?
    }

    fn unwatch_inner(&mut self, path: &Path) -> Result<()> {
        let pb = absolute_path(path)?;
        let (tx, rx) = unbounded();
        let msg = EventLoopMsg::RemoveWatch(pb, tx);

        self.channel.send(msg)?;
        self.waker.wake()?;
        rx.recv().map_err(Error::from)?
    }

    /// One channel send, one wake and one reply for the whole batch, instead of one round trip
    /// to the loop thread per path.
    ///
    /// Per-op results match the default [`Watcher::update_paths`]: ops run in order and the first
    /// failure (including `MaxFilesWatch` or `PathNotFound` for that op) is returned as `origin`,
    /// with every later op in `remaining`. The one difference is a dead loop thread: when the
    /// channel or waker fails after the batch was handed over, it is unknown which ops ran, so
    /// the error carries no `origin` and no `remaining`. A batch that could not be handed over at
    /// all is returned whole, as the default would after its first op failed to send.
    fn update_paths_inner(&mut self, ops: Vec<PathOp>) -> StdResult<(), UpdatePathsError> {
        if ops.is_empty() {
            return Ok(());
        }
        let ops = ops.into_iter().map(ResolvedPathOp::new).collect();
        let (tx, rx) = unbounded();
        if let Err(std::sync::mpsc::SendError(msg)) =
            self.channel.send(EventLoopMsg::UpdatePaths(ops, tx))
        {
            let ops = match msg {
                EventLoopMsg::UpdatePaths(ops, _) => {
                    ops.into_iter().map(|resolved| resolved.op).collect()
                }
                _ => Vec::new(),
            };
            let source = Error::from(std::sync::mpsc::SendError(()));
            let mut ops = ops.into_iter();
            return Err(UpdatePathsError {
                source,
                origin: ops.next(),
                remaining: ops.collect(),
            });
        }
        let lost = |source: Error| UpdatePathsError {
            source,
            origin: None,
            remaining: Vec::new(),
        };
        self.waker.wake().map_err(|e| lost(e.into()))?;
        rx.recv().map_err(|e| lost(e.into()))?
    }

    fn watched_paths_inner(&self) -> Result<Vec<(PathBuf, RecursiveMode)>> {
        let (tx, rx) = unbounded();
        self.channel.send(EventLoopMsg::GetWatchedPaths(tx))?;
        self.waker.wake()?;
        rx.recv().map_err(Error::from)
    }
}

impl Watcher for INotifyWatcher {
    /// Create a new watcher.
    fn new<F: EventHandler>(event_handler: F, config: Config) -> Result<Self> {
        Self::from_event_handler(Box::new(event_handler), &config)
    }

    fn watch(&mut self, path: &Path, recursive_mode: RecursiveMode) -> Result<()> {
        self.watch_inner(path, WatchPathConfig::new(recursive_mode))
    }

    fn watch_with(&mut self, path: &Path, config: WatchPathConfig) -> Result<()> {
        self.watch_inner(path, config)
    }

    fn unwatch(&mut self, path: &Path) -> Result<()> {
        self.unwatch_inner(path)
    }

    fn update_paths(&mut self, ops: Vec<PathOp>) -> StdResult<(), UpdatePathsError> {
        self.update_paths_inner(ops)
    }

    fn configure(&mut self, config: Config) -> Result<bool> {
        let (tx, rx) = bounded(1);
        self.channel.send(EventLoopMsg::Configure(config, tx))?;
        self.waker.wake()?;
        rx.recv()?
    }

    fn watched_paths(&self) -> Result<Vec<(PathBuf, RecursiveMode)>> {
        self.watched_paths_inner()
    }

    fn kind() -> crate::WatcherKind {
        crate::WatcherKind::Inotify
    }
}

impl Drop for INotifyWatcher {
    fn drop(&mut self) {
        // we expect the event loop to live => unwrap must not panic
        self.channel.send(EventLoopMsg::Shutdown).unwrap();
        self.waker.wake().unwrap();
    }
}

#[cfg(test)]
mod tests {
    use std::{
        path::{Path, PathBuf},
        sync::{Arc, atomic::AtomicBool, mpsc},
        thread::{self, available_parallelism},
        time::Duration,
    };

    use super::inotify_sys::WatchMask;
    use super::{
        Config, Error, ErrorKind, Event, EventKind, EventLoop, INotifyWatcher, RecursiveMode,
        Result, WatchPath, WatchPathConfig, Watcher,
    };
    use notify_types::event::{EventKindMask, RemoveKind};

    use crate::test::*;

    /// Only data changes, so access events do not disturb exact assertions.
    fn watcher_with_data_events() -> (TestWatcher<INotifyWatcher>, Receiver) {
        channel_with_config(
            ChannelConfig::default().with_watcher_config(
                Config::default().with_event_kinds(EventKindMask::MODIFY_DATA),
            ),
        )
    }

    fn recursive_watch() -> WatchPathConfig {
        WatchPathConfig::new(RecursiveMode::Recursive)
    }

    fn non_recursive_watch() -> WatchPathConfig {
        WatchPathConfig::new(RecursiveMode::NonRecursive)
    }

    fn watcher() -> (TestWatcher<INotifyWatcher>, Receiver) {
        channel()
    }

    fn test_event_loop_with_config(config: &Config) -> EventLoop {
        let inotify = super::inotify_sys::Inotify::init().unwrap();
        EventLoop::new(inotify, Box::new(|_| {}), config).unwrap()
    }

    fn test_event_loop() -> EventLoop {
        test_event_loop_with_config(&Config::default())
    }

    /// Create a watcher configured to receive ALL events including Access events.
    /// Use this for tests that verify Access event behavior.
    fn watcher_with_all_events() -> (TestWatcher<INotifyWatcher>, Receiver) {
        channel_with_config(
            ChannelConfig::default()
                .with_timeout(std::time::Duration::from_secs(1))
                .with_watcher_config(Config::default().with_event_kinds(EventKindMask::ALL)),
        )
    }

    #[test]
    fn inotify_watcher_is_send_and_sync() {
        fn check<T: Send + Sync>() {}
        check::<INotifyWatcher>();
    }

    #[test]
    fn native_error_type_on_missing_path() {
        let mut watcher = INotifyWatcher::new(|_| {}, Config::default()).unwrap();

        let result = watcher.watch(
            &PathBuf::from("/some/non/existant/path"),
            RecursiveMode::NonRecursive,
        );

        assert!(matches!(
            result,
            Err(Error {
                paths: _,
                kind: ErrorKind::PathNotFound
            })
        ))
    }

    #[test]
    fn stored_watch_mask_keeps_no_resolution_flags() {
        let tmpdir = tempfile::tempdir().unwrap();
        let root = tmpdir.path().to_path_buf();
        let child = root.join("child");
        std::fs::create_dir(&child).unwrap();

        let inotify = super::inotify_sys::Inotify::init().unwrap();
        let mut event_loop = EventLoop::new(inotify, Box::new(|_| {}), &Config::default()).unwrap();

        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), recursive_watch(), true)
            .expect("watch recursively");
        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), non_recursive_watch(), true)
            .expect("rewatch non-recursively");

        for (path, watch) in &event_loop.watches {
            assert!(
                !watch.watch_mask.intersects(super::RESOLUTION_FLAGS),
                "{path:?} stored {:?}",
                watch.watch_mask
            );
        }
    }

    // Regression test for https://github.com/notify-rs/notify/issues/579.
    #[test]
    fn recursive_watch_ignores_missing_subdir_during_initial_scan() {
        use std::fs;

        let tmpdir = tempfile::tempdir().unwrap();
        let root = tmpdir.path().to_path_buf();
        let disappearing = root.join("disappearing");
        fs::create_dir(&disappearing).unwrap();
        fs::remove_dir_all(&disappearing).unwrap();

        let mut event_loop = test_event_loop();

        // Simulate the TOCTOU: we *intend* to watch a subdirectory discovered during initial scan,
        // but it's already gone by the time we call `inotify_add_watch`.
        let result = event_loop.add_watches_for_paths(
            [root, disappearing]
                .into_iter()
                .map(|path| WatchPath::new(&path).unwrap()),
            true,
            true,
            true,
        );
        assert!(
            result.is_ok(),
            "expected recursive watch to succeed, got: {result:?}"
        );
    }

    #[test]
    fn rewatching_same_path_replaces_recursive_state() {
        let tmpdir = tempfile::tempdir().unwrap();
        let root = tmpdir.path().to_path_buf();
        let child = root.join("child");
        std::fs::create_dir(&child).unwrap();

        let mut event_loop = test_event_loop();

        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), recursive_watch(), true)
            .expect("watch recursively");
        assert!(event_loop.watches.contains_key(&child));

        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), non_recursive_watch(), true)
            .expect("rewatch non-recursively");

        let watch = event_loop.watches.get(&root).expect("root watch");
        assert!(watch.metadata.is_user_watch);
        assert!(!watch.metadata.user_is_recursive);
        assert!(!watch.metadata.is_recursive);
        assert!(!event_loop.watches.contains_key(&child));
    }

    #[test]
    fn rewatching_child_preserves_recursive_parent_state() {
        let tmpdir = tempfile::tempdir().unwrap();
        let root = tmpdir.path().to_path_buf();
        let child = root.join("child");
        let grandchild = child.join("grandchild");
        std::fs::create_dir_all(&grandchild).unwrap();

        let mut event_loop = test_event_loop();

        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), recursive_watch(), true)
            .expect("watch root recursively");
        event_loop
            .add_watch(WatchPath::new(&child).unwrap(), non_recursive_watch(), true)
            .expect("watch child non-recursively");
        event_loop
            .add_watch(
                WatchPath::from_parts(child.clone(), PathBuf::from("reported-child")),
                non_recursive_watch(),
                true,
            )
            .expect("rewatch child non-recursively");

        let child_watch = event_loop.watches.get(&child).expect("child watch");
        assert!(child_watch.metadata.is_user_watch);
        assert!(!child_watch.metadata.user_is_recursive);
        assert!(child_watch.metadata.is_recursive);
        assert_eq!(
            child_watch.metadata.reported_path,
            PathBuf::from("reported-child")
        );

        let grandchild_watch = event_loop
            .watches
            .get(&grandchild)
            .expect("grandchild still covered by recursive parent");
        assert!(!grandchild_watch.metadata.is_user_watch);
        assert!(grandchild_watch.metadata.is_recursive);
    }

    #[test]
    fn rewatching_carved_out_child_does_not_restore_parent_recursive_state() {
        let tmpdir = tempfile::tempdir().unwrap();
        let root = tmpdir.path().to_path_buf();
        let child = root.join("child");
        let grandchild = child.join("grandchild");
        std::fs::create_dir_all(&grandchild).unwrap();

        let mut event_loop = test_event_loop();

        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), recursive_watch(), true)
            .expect("watch root recursively");
        event_loop
            .remove_watch(child.clone(), false)
            .expect("carve out child");
        event_loop
            .add_watch(WatchPath::new(&child).unwrap(), non_recursive_watch(), true)
            .expect("watch child non-recursively");
        event_loop
            .add_watch(
                WatchPath::from_parts(child.clone(), PathBuf::from("reported-child")),
                non_recursive_watch(),
                true,
            )
            .expect("rewatch child non-recursively");

        let child_watch = event_loop.watches.get(&child).expect("child watch");
        assert!(child_watch.metadata.is_user_watch);
        assert!(!child_watch.metadata.user_is_recursive);
        assert!(!child_watch.metadata.is_recursive);
        assert_eq!(
            child_watch.metadata.reported_path,
            PathBuf::from("reported-child")
        );
        assert!(!event_loop.watches.contains_key(&grandchild));
    }

    /// Runs manually.
    ///
    /// * Save actual value of the limit: `MAX_USER_WATCHES=$(sysctl -n fs.inotify.max_user_watches)`
    /// * Run the test.
    /// * Set the limit to 0: `sudo sysctl fs.inotify.max_user_watches=0` while test is running
    /// * Wait for the test to complete
    /// * Restore the limit `sudo sysctl fs.inotify.max_user_watches=$MAX_USER_WATCHES`
    #[test]
    #[ignore = "requires changing sysctl fs.inotify.max_user_watches while test is running"]
    fn recursive_watch_calls_handler_if_creating_a_file_raises_max_files_watch() {
        use std::time::Duration;

        let tmpdir = tempfile::tempdir().unwrap();
        let (tx, rx) = std::sync::mpsc::channel();
        let (proc_changed_tx, proc_changed_rx) = std::sync::mpsc::channel();
        let proc_path = Path::new("/proc/sys/fs/inotify/max_user_watches");
        let mut watcher = INotifyWatcher::new(
            move |result: Result<Event>| match result {
                Ok(event) => {
                    if event.paths.first().is_some_and(|path| path == proc_path) {
                        proc_changed_tx.send(()).unwrap();
                    }
                }
                Err(e) => tx.send(e).unwrap(),
            },
            Config::default(),
        )
        .unwrap();

        watcher
            .watch(tmpdir.path(), RecursiveMode::Recursive)
            .unwrap();
        watcher
            .watch(proc_path, RecursiveMode::NonRecursive)
            .unwrap();

        // give the time to set the limit
        proc_changed_rx
            .recv_timeout(Duration::from_secs(30))
            .unwrap();

        let child_dir = tmpdir.path().join("child");
        std::fs::create_dir(child_dir).unwrap();

        let result = rx.recv_timeout(Duration::from_millis(500));

        assert!(
            matches!(
                &result,
                Ok(Error {
                    kind: ErrorKind::MaxFilesWatch,
                    paths: _,
                })
            ),
            "expected {:?}, found: {:#?}",
            ErrorKind::MaxFilesWatch,
            result
        );
    }

    /// https://github.com/notify-rs/notify/issues/678
    #[test]
    fn race_condition_on_unwatch_and_pending_events_with_deleted_descriptor() {
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let (tx, rx) = mpsc::channel();
        // Use CORE to exclude access events - the parallel threads opening files
        // would otherwise flood the queue with OPEN events causing Rescan
        let mut inotify = INotifyWatcher::new(
            move |e: Result<Event>| {
                let e = match e {
                    Ok(e) if e.paths.is_empty() => e,
                    Ok(_) | Err(_) => return,
                };
                let _ = tx.send(e);
            },
            Config::default().with_event_kinds(EventKindMask::CORE),
        )
        .expect("inotify creation");

        let dir_path = tmpdir.path();
        let file_path = dir_path.join("foo");
        std::fs::File::create(&file_path).unwrap();

        let stop = Arc::new(AtomicBool::new(false));

        let handles: Vec<_> = (0..available_parallelism().unwrap().get().max(4))
            .map(|_| {
                let file_path = file_path.clone();
                let stop = stop.clone();
                thread::spawn(move || {
                    while !stop.load(std::sync::atomic::Ordering::Relaxed) {
                        let _ = std::fs::File::open(&file_path).unwrap();
                    }
                })
            })
            .collect();

        let non_recursive = RecursiveMode::NonRecursive;
        for _ in 0..(handles.len() * 4) {
            inotify.watch(dir_path, non_recursive).unwrap();
            inotify.unwatch(dir_path).unwrap();
        }

        stop.store(true, std::sync::atomic::Ordering::Relaxed);
        handles
            .into_iter()
            .for_each(|handle| handle.join().ok().unwrap_or_default());

        drop(inotify);

        let events: Vec<_> = rx.into_iter().map(|e| format!("{e:?}")).collect();

        const LOG_LEN: usize = 10;
        let events_len = events.len();
        assert!(
            events.is_empty(),
            "expected no events without path, but got {events_len}. first 10: {:#?}",
            &events[..LOG_LEN.min(events_len)]
        );
    }

    /// https://github.com/notify-rs/notify/issues/709
    #[test]
    fn remove_a_subdir_in_a_recursively_watched_parent() {
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let subdirectory_path_1 = tmpdir.path().join("subdir");
        let subdirectory_path_2 = subdirectory_path_1.join("nested");
        std::fs::create_dir(&subdirectory_path_1).expect("unable to create a subdir");
        std::fs::create_dir(&subdirectory_path_2).expect("unable to create a nested dir");

        let mut watcher =
            INotifyWatcher::new(|_| (), Config::default()).expect("unable to create watcher");
        watcher
            .watch(tmpdir.path(), RecursiveMode::Recursive)
            .expect("unable to watch");
        std::fs::remove_dir_all(&subdirectory_path_1).expect("unable to remove a subdir");
        let unwatch_result = watcher.unwatch(tmpdir.path());

        assert!(
            matches!(unwatch_result, Ok(())),
            "error: {unwatch_result:#?}"
        );
    }

    // FIXME: FreeBSD 15.1 does not generate IN_IGNORED unless IN_DELETE_SELF was requested.
    // Remove this ignore once CI uses a release containing the fix:
    // https://cgit.freebsd.org/src/commit/?id=242c9c86c8cad6aa29bc1af9161d4f0eec45f29b
    #[cfg_attr(
        target_os = "freebsd",
        ignore = "FreeBSD 15.1 does not generate IN_IGNORED unconditionally"
    )]
    #[test]
    fn ignored_event_removes_watch_when_remove_events_are_filtered_out() {
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let root = tmpdir.path().to_path_buf();
        let child = root.join("child");
        std::fs::create_dir(&child).expect("create child");

        // Recursive setup still installs a watch for `child`, but the parent does not receive a
        // DELETE event with this mask. IGNORED is therefore the only cleanup signal and must be
        // handled independently of the user-visible event filter.
        let config = Config::default().with_event_kinds(EventKindMask::MODIFY_DATA);
        let mut event_loop = test_event_loop_with_config(&config);
        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), recursive_watch(), true)
            .expect("watch recursively");

        let child_descriptor = event_loop
            .watches
            .get(&child)
            .expect("child watch")
            .watch_descriptor
            .clone();

        std::fs::remove_dir(&child).expect("remove child");
        event_loop.handle_inotify();

        assert!(event_loop.watches.contains_key(&root));
        assert!(
            !event_loop.watches.contains_key(&child),
            "IGNORED must remove the stale child watch"
        );
        assert!(
            !event_loop.paths.contains_key(&child_descriptor),
            "IGNORED must remove the stale descriptor-to-path mapping"
        );
    }

    #[test]
    fn duplicate_watch_removals_are_coalesced() {
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let path = tmpdir.path().to_path_buf();
        let mut event_loop = test_event_loop();
        event_loop
            .add_watch(WatchPath::new(&path).unwrap(), non_recursive_watch(), true)
            .expect("add_watch");

        // DELETE may queue a normal removal before DELETE_SELF or IGNORED confirms that the
        // kernel already removed the same descriptor. Keep one entry with the stronger mode.
        let mut queued = std::collections::BTreeMap::new();
        for removal in [
            super::WatchRemoval::WithOsCall,
            super::WatchRemoval::DescriptorAlreadyRemoved,
        ] {
            super::queue_watch_removal(&path, None, &event_loop.watches, &mut queued, removal);
        }

        assert_eq!(
            queued.into_iter().collect::<Vec<_>>(),
            vec![(path, super::WatchRemoval::DescriptorAlreadyRemoved)]
        );
    }

    #[test]
    fn deleting_parent_still_removes_live_moved_out_descendant_descriptor() {
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let root = tmpdir.path().join("root");
        let child = root.join("child");
        let moved_child = tmpdir.path().join("moved-child");
        std::fs::create_dir_all(&child).expect("create watched tree");

        // Excluding rename/remove events deliberately leaves the moved child's old path in the
        // recursive bookkeeping until deleting the root triggers descriptor cleanup. Unlike the
        // deleted root descriptor, the descriptor follows the moved child and remains live.
        let config = Config::default().with_event_kinds(EventKindMask::MODIFY_DATA);
        let mut event_loop = test_event_loop_with_config(&config);
        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), recursive_watch(), true)
            .expect("watch recursively");

        let child_descriptor = event_loop
            .watches
            .get(&child)
            .expect("child watch")
            .watch_descriptor
            .clone();

        std::fs::rename(&child, &moved_child).expect("move child out of watched root");
        std::fs::remove_dir(&root).expect("remove watched root");
        event_loop.handle_inotify();

        assert!(event_loop.watches.is_empty());
        assert!(event_loop.paths.is_empty());

        // EINVAL here is expected because recursive cleanup should already have issued rm_watch
        // for the live moved-out descendant. Skipping every syscall for a deleted root would leak
        // that descriptor even though the local maps looked empty.
        let remove_result = event_loop
            .inotify
            .as_mut()
            .expect("inotify instance")
            .watches()
            .remove(child_descriptor);
        assert_eq!(
            remove_result.unwrap_err().raw_os_error(),
            Some(libc::EINVAL),
            "the moved-out descendant descriptor must already have been removed"
        );
    }

    #[test]
    fn unmount_event_maps_to_remove_other_with_unmount_info() {
        let path = PathBuf::from("/tmp/notify-unmount");
        let event = super::unmount_event(path.clone());

        assert_eq!(event.kind, EventKind::Remove(RemoveKind::Other));
        assert_eq!(event.paths, vec![path]);
        assert_eq!(event.info(), Some("unmount"));
    }

    #[test]
    fn descriptor_removed_cleanup_removes_internal_state() {
        let tmpdir = tempfile::tempdir().unwrap();
        let watched = tmpdir.path().join("watched");
        std::fs::create_dir(&watched).unwrap();

        let mut event_loop = test_event_loop();

        event_loop
            .add_watch(
                WatchPath::new(&watched).unwrap(),
                non_recursive_watch(),
                true,
            )
            .expect("add_watch");

        event_loop
            .remove_watch_without_root_os_call(watched.clone(), true)
            .expect("remove_watch_without_root_os_call");

        let result = event_loop.remove_watch(watched.clone(), false);
        assert!(
            matches!(
                result,
                Err(Error {
                    kind: ErrorKind::WatchNotFound,
                    ..
                })
            ),
            "expected WatchNotFound, got: {result:?}"
        );
    }

    #[test]
    fn create_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_all_events();
        watcher.watch_recursively(&tmpdir);

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).create_file(),
            expected(&path).access_open_any(),
            expected(&path).access_close_write(),
        ]);
    }

    #[test]
    fn write_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_all_events();

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        watcher.watch_recursively(&tmpdir);
        std::fs::write(&path, b"123").expect("write");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).access_open_any(),
            expected(&path).modify_data_any().multiple(),
            expected(&path).access_close_write(),
        ]);
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

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([expected(&path).modify_meta_any()]);
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

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).rename_from(),
            expected(&new_path).rename_to(),
            expected([path, new_path]).rename_both(),
        ])
        .ensure_trackers_len(1);
    }

    #[test]
    fn delete_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        let file = tmpdir.path().join("file");
        std::fs::write(&file, "").expect("write");

        watcher.watch_nonrecursively(&tmpdir);

        std::fs::remove_file(&file).expect("remove");

        rx.wait_ordered_exact([expected(&file).remove_file()]);
    }

    #[test]
    fn delete_self_file() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        let file = tmpdir.path().join("file");
        std::fs::write(&file, "").expect("write");

        watcher.watch_nonrecursively(&file);

        std::fs::remove_file(&file).expect("remove");

        rx.wait_ordered_exact([
            expected(&file).modify_meta_any(),
            expected(&file).remove_file(),
        ]);
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
        let (mut watcher, mut rx) = watcher_with_all_events();
        let overwritten_file = tmpdir.path().join("overwritten_file");
        let overwriting_file = tmpdir.path().join("overwriting_file");
        std::fs::write(&overwritten_file, "123").expect("write1");

        watcher.watch_nonrecursively(&tmpdir);

        std::fs::File::create(&overwriting_file).expect("create");
        std::fs::write(&overwriting_file, "321").expect("write2");
        std::fs::rename(&overwriting_file, &overwritten_file).expect("rename");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&overwriting_file).create_file(),
            expected(&overwriting_file).access_open_any(),
            expected(&overwriting_file).access_close_write(),
            expected(&overwriting_file).access_open_any(),
            expected(&overwriting_file).modify_data_any().multiple(),
            expected(&overwriting_file).access_close_write(),
            expected(&overwriting_file).rename_from(),
            expected(&overwritten_file).rename_to(),
            expected([overwriting_file, overwritten_file]).rename_both(),
        ])
        .ensure_trackers_len(1);
    }

    #[test]
    fn create_dir() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();
        watcher.watch_recursively(&tmpdir);

        let path = tmpdir.path().join("entry");
        std::fs::create_dir(&path).expect("create");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([expected(&path).create_folder()]);
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

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).access_open_any().optional(),
            expected(&path).modify_meta_any(),
            expected(&path).modify_meta_any(),
        ]);
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

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).access_open_any().optional(),
            expected(&path).rename_from(),
            expected(&new_path).rename_to(),
            expected([path, new_path]).rename_both(),
        ])
        .ensure_trackers_len(1);
    }

    #[test]
    fn delete_dir() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let path = tmpdir.path().join("entry");
        std::fs::create_dir(&path).expect("create_dir");

        watcher.watch_recursively(&tmpdir);
        std::fs::remove_dir(&path).expect("remove");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).access_open_any().optional(),
            expected(&path).remove_folder(),
        ]);
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

        // Use wait_ordered (not _exact) because we may get extra events
        // due to directory traversal/rescan on rename
        rx.wait_ordered([
            expected(&path).access_open_any().optional(),
            expected(&path).rename_from(),
            expected(&new_path).rename_to(),
            expected([&path, &new_path]).rename_both(),
            expected(&new_path).access_open_any().optional(),
            expected(&new_path).rename_from(),
            expected(&new_path2).rename_to(),
            expected([&new_path, &new_path2]).rename_both(),
        ])
        .ensure_trackers_len(2);
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

        // With ALL events, we may get Access events on the directory.
        // Skip Access events to find the rename event.
        let event = loop {
            let event = rx.recv();
            if !matches!(event.kind, EventKind::Access(_)) {
                break event;
            }
        };
        let tracker = event.attrs.tracker();
        assert_eq!(event, expected(&path).rename_from());
        assert!(tracker.is_some(), "tracker is none: {event:#?}");
    }

    #[test]
    fn create_write_write_rename_write_remove() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_all_events();

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

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&file1).create_file(),
            expected(&file1).access_open_any(),
            expected(&file1).modify_data_any().multiple(),
            expected(&file1).access_close_write(),
            expected(&file2).access_open_any(),
            expected(&file2).modify_data_any().multiple(),
            expected(&file2).access_close_write(),
            expected(&file1).access_open_any().optional(),
            expected(&file1).rename_from(),
            expected(&new_path).rename_to(),
            expected([&file1, &new_path]).rename_both(),
            expected(&new_path).access_open_any(),
            expected(&new_path).modify_data_any().multiple(),
            expected(&new_path).access_close_write(),
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

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).access_open_any().optional(),
            expected(&path).rename_from(),
            expected(&new_path1).rename_to(),
            expected([&path, &new_path1]).rename_both(),
            expected(&new_path1).access_open_any().optional(),
            expected(&new_path1).rename_from(),
            expected(&new_path2).rename_to(),
            expected([&new_path1, &new_path2]).rename_both(),
        ])
        .ensure_trackers_len(2);
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

        // With ALL events, we may get Access events on the directory.
        // Skip Access events to find the modify event.
        let event = loop {
            let event = rx.recv();
            if !matches!(event.kind, EventKind::Access(_)) {
                break event;
            }
        };
        // Linux and FreeBSD classify this modification differently.
        assert_eq!(event, expected(&path).modify());
    }

    #[test]
    fn write_file_non_recursive_watch() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_all_events();

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        watcher.watch_nonrecursively(&path);

        std::fs::write(&path, b"123").expect("write");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&path).access_open_any(),
            expected(&path).modify_data_any().multiple(),
            expected(&path).access_close_write(),
        ]);
    }

    #[test]
    fn watch_recursively_then_unwatch_child_stops_events_from_child() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_all_events();

        let subdir = tmpdir.path().join("subdir");
        let file = subdir.join("file");
        std::fs::create_dir(&subdir).expect("create");

        watcher.watch_recursively(&tmpdir);

        std::fs::File::create(&file).expect("create");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&subdir).access_open_any().optional(),
            expected(&file).create_file(),
            expected(&file).access_open_any(),
            expected(&file).access_close_write(),
        ]);

        watcher.watcher.unwatch(&subdir).expect("unwatch");

        std::fs::write(&file, b"123").expect("write");

        std::fs::remove_dir_all(&subdir).expect("remove_dir_all");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&subdir).access_open_any().optional(),
            expected(&subdir).remove_folder(),
        ]);
    }

    #[test]
    fn write_to_a_hardlink_pointed_to_the_watched_file_triggers_an_event() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_all_events();

        let subdir = tmpdir.path().join("subdir");
        let file = subdir.join("file");
        let hardlink = tmpdir.path().join("hardlink");

        std::fs::create_dir(&subdir).expect("create");
        std::fs::write(&file, "").expect("file");
        std::fs::hard_link(&file, &hardlink).expect("hardlink");

        watcher.watch_nonrecursively(&file);

        std::fs::write(&hardlink, "123123").expect("write to the hard link");

        // Use wait_ordered (not _exact) because with ALL events we may get
        // directory access events that are timing-dependent
        rx.wait_ordered([
            expected(&file).access_open_any(),
            expected(&file).modify_data_any().multiple(),
            expected(&file).access_close_write(),
        ]);
    }

    // FreeBSD reports writes through any hard link to the watched inode.
    #[test]
    #[cfg(not(target_os = "freebsd"))]
    fn write_to_a_hardlink_pointed_to_the_file_in_the_watched_dir_doesnt_trigger_an_event() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher();

        let subdir = tmpdir.path().join("subdir");
        let file = subdir.join("file");
        let hardlink = tmpdir.path().join("hardlink");

        std::fs::create_dir(&subdir).expect("create");
        std::fs::write(&file, "").expect("file");
        std::fs::hard_link(&file, &hardlink).expect("hardlink");

        watcher.watch_nonrecursively(&subdir);

        std::fs::write(&hardlink, "123123").expect("write to the hard link");

        // With ALL events, we may get Access events on the watched directory.
        // Filter those out - we only care about non-Access events on the file.
        let events: Vec<_> = rx
            .iter()
            .filter(|e| !matches!(e.kind, EventKind::Access(_)))
            .collect();
        assert!(events.is_empty(), "unexpected events: {events:#?}");
    }

    #[test]
    #[ignore = "see https://github.com/notify-rs/notify/issues/727"]
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

    // ============================================================
    // EventKindMask filtering tests
    // ============================================================

    /// Test that CORE config does not produce Access events.
    #[test]
    fn event_kind_mask_core_config_no_access_events() {
        let tmpdir = testdir();
        // Use explicit CORE mask to exclude access events
        let (mut watcher, mut rx) = channel_with_config::<INotifyWatcher>(
            ChannelConfig::default()
                .with_timeout(std::time::Duration::from_secs(1))
                .with_watcher_config(Config::default().with_event_kinds(EventKindMask::CORE)),
        );
        watcher.watch_recursively(&tmpdir);

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        // With CORE config, we should only get create event, no access events
        rx.wait_ordered_exact([expected(&path).create_file()])
            .ensure_no_tail();
    }

    /// Test that EventKindMask::ALL config produces Access events.
    #[test]
    fn event_kind_mask_all_config_produces_access_events() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_all_events();
        watcher.watch_recursively(&tmpdir);

        let path = tmpdir.path().join("entry");
        std::fs::File::create_new(&path).expect("create");

        // With ALL config, we should get create + access events
        // Use wait_ordered (not _exact) because we may get directory access events too
        rx.wait_ordered([
            expected(&path).create_file(),
            expected(&path).access_open_any(),
            expected(&path).access_close_write(),
        ]);
    }

    /// Test that CREATE | REMOVE only mask filters out Modify events.
    #[test]
    fn event_kind_mask_create_remove_only_no_modify() {
        let tmpdir = testdir();
        let mask = EventKindMask::CREATE | EventKindMask::REMOVE;
        let (mut watcher, mut rx) = channel_with_config::<INotifyWatcher>(
            ChannelConfig::default()
                .with_timeout(std::time::Duration::from_secs(1))
                .with_watcher_config(Config::default().with_event_kinds(mask)),
        );
        watcher.watch_recursively(&tmpdir);

        let path = tmpdir.path().join("entry");
        std::fs::write(&path, b"123").expect("write");

        // With CREATE | REMOVE mask, we should only get create event, no modify events
        rx.wait_ordered_exact([expected(&path).create_file()])
            .ensure_no_tail();
    }

    /// Test unit tests for event_kind_mask_to_watch_mask helper function.
    #[test]
    fn event_kind_mask_to_watch_mask_core() {
        use super::event_kind_mask_to_watch_mask;

        let mask = EventKindMask::CORE;
        let watch_mask = event_kind_mask_to_watch_mask(mask, false);

        // CORE includes CREATE, REMOVE, MODIFY_DATA, MODIFY_META, MODIFY_NAME
        assert!(watch_mask.intersects(WatchMask::CREATE));
        assert!(watch_mask.intersects(WatchMask::MOVED_TO));
        assert!(watch_mask.intersects(WatchMask::DELETE));
        assert!(watch_mask.intersects(WatchMask::MOVED_FROM));
        assert!(watch_mask.intersects(WatchMask::MODIFY));
        assert!(watch_mask.intersects(WatchMask::ATTRIB));
        assert!(watch_mask.intersects(WatchMask::MOVE_SELF));

        // CORE does NOT include ACCESS (OPEN, CLOSE_WRITE, CLOSE_NOWRITE)
        // Note: CLOSE_WRITE generates Access events, not Modify events
        assert!(!watch_mask.intersects(WatchMask::OPEN));
        assert!(!watch_mask.intersects(WatchMask::CLOSE_WRITE));
        assert!(!watch_mask.intersects(WatchMask::CLOSE_NOWRITE));
    }

    #[test]
    fn event_kind_mask_to_watch_mask_all() {
        use super::event_kind_mask_to_watch_mask;

        let mask = EventKindMask::ALL;
        let watch_mask = event_kind_mask_to_watch_mask(mask, false);

        // ALL includes everything from CORE plus ACCESS
        assert!(watch_mask.intersects(WatchMask::OPEN));
        assert!(watch_mask.intersects(WatchMask::CLOSE_WRITE));
        assert!(watch_mask.intersects(WatchMask::CLOSE_NOWRITE));
    }

    #[test]
    fn event_kind_mask_to_watch_mask_empty() {
        use super::event_kind_mask_to_watch_mask;

        let mask = EventKindMask::empty();
        let watch_mask = event_kind_mask_to_watch_mask(mask, false);

        // Empty mask should produce empty watch mask
        assert!(watch_mask.is_empty());
    }

    #[test]
    fn event_kind_mask_to_watch_mask_access_only() {
        use super::event_kind_mask_to_watch_mask;

        // ACCESS_CLOSE only maps to CLOSE_WRITE (not CLOSE_NOWRITE)
        let mask = EventKindMask::ACCESS_OPEN | EventKindMask::ACCESS_CLOSE;
        let watch_mask = event_kind_mask_to_watch_mask(mask, false);

        assert!(watch_mask.intersects(WatchMask::OPEN));
        assert!(watch_mask.intersects(WatchMask::CLOSE_WRITE));
        assert!(!watch_mask.intersects(WatchMask::CLOSE_NOWRITE));

        // Should NOT have create/modify/remove
        assert!(!watch_mask.intersects(WatchMask::CREATE));
        assert!(!watch_mask.intersects(WatchMask::DELETE));
        assert!(!watch_mask.intersects(WatchMask::MODIFY));
        assert!(!watch_mask.intersects(WatchMask::ATTRIB));
    }

    #[test]
    fn event_kind_mask_to_watch_mask_all_access() {
        use super::event_kind_mask_to_watch_mask;

        // ALL_ACCESS includes OPEN, CLOSE_WRITE, and CLOSE_NOWRITE
        let mask = EventKindMask::ALL_ACCESS;
        let watch_mask = event_kind_mask_to_watch_mask(mask, false);

        assert!(watch_mask.intersects(WatchMask::OPEN));
        assert!(watch_mask.intersects(WatchMask::CLOSE_WRITE));
        assert!(watch_mask.intersects(WatchMask::CLOSE_NOWRITE));
    }

    #[test]
    fn event_kind_mask_to_watch_mask_recursive_includes_create() {
        use super::event_kind_mask_to_watch_mask;

        // Recursive mode includes CREATE|MOVED_TO even without CREATE in mask
        let watch_mask = event_kind_mask_to_watch_mask(EventKindMask::MODIFY_DATA, true);
        assert!(watch_mask.intersects(WatchMask::CREATE));
        assert!(watch_mask.intersects(WatchMask::MOVED_TO));
        assert!(watch_mask.intersects(WatchMask::MODIFY));

        // Empty mask with recursive still includes CREATE|MOVED_TO
        let watch_mask = event_kind_mask_to_watch_mask(EventKindMask::empty(), true);
        assert!(watch_mask.intersects(WatchMask::CREATE));
        assert!(watch_mask.intersects(WatchMask::MOVED_TO));
        assert!(!watch_mask.intersects(WatchMask::MODIFY));

        // Non-recursive mode does not include CREATE when not requested
        let watch_mask = event_kind_mask_to_watch_mask(EventKindMask::MODIFY_DATA, false);
        assert!(!watch_mask.intersects(WatchMask::CREATE));
        assert!(!watch_mask.intersects(WatchMask::MOVED_TO));
        assert!(watch_mask.intersects(WatchMask::MODIFY));
    }

    /// Recursive watches with MODIFY-only mask still track new subdirectories.
    #[test]
    fn recursive_watch_tracks_subdirs_without_create_mask() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = channel_with_config::<INotifyWatcher>(
            ChannelConfig::default()
                .with_timeout(std::time::Duration::from_secs(2))
                .with_watcher_config(
                    Config::default().with_event_kinds(EventKindMask::MODIFY_DATA),
                ),
        );
        watcher.watch_recursively(&tmpdir);

        let subdir = tmpdir.path().join("subdir");
        std::fs::create_dir(&subdir).expect("create subdir");

        // Wait for watch to be added on new subdirectory
        std::thread::sleep(std::time::Duration::from_millis(50));

        let file_path = subdir.join("file.txt");
        let mut file = std::fs::File::create_new(&file_path).expect("create file");

        use std::io::Write;
        file.write_all(b"hello").expect("write");
        file.flush().expect("flush");
        drop(file);

        // Receives MODIFY from subdir (tracking works), no CREATE events (filtered)
        rx.wait_ordered_exact([expected(&file_path).modify_data()])
            .ensure_no_tail();
    }

    /// A recursive watch resolves the path it walks, so the flag cannot silence it.
    #[test]
    fn recursive_watch_of_a_symlinked_dir_without_dereference_still_walks() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_data_events();
        let destination = tmpdir.path().join("destination");
        std::fs::create_dir(&destination).expect("create");
        let file = destination.join("file");
        std::fs::write(&file, "").expect("write");
        let link = tmpdir.path().join("link");
        std::os::unix::fs::symlink(&destination, &link).expect("symlink");

        watcher
            .watcher
            .watch_with(&link, recursive_watch().with_dereference_symlinks(false))
            .expect("watch link recursively");

        std::fs::write(&file, "123").expect("write");

        rx.wait_ordered([expected(link.join("file")).modify_data_any().multiple()]);
    }

    // Regression tests for https://github.com/notify-rs/notify/issues/255.
    #[test]
    fn watching_a_dangling_symlink_without_dereference() {
        let tmpdir = tempfile::tempdir().unwrap();
        let link = tmpdir.path().join("link");
        std::os::unix::fs::symlink(tmpdir.path().join("missing"), &link).unwrap();

        let inotify = super::inotify_sys::Inotify::init().unwrap();
        let mut event_loop = EventLoop::new(inotify, Box::new(|_| {}), &Config::default()).unwrap();

        event_loop
            .add_watch(
                WatchPath::new(&link).unwrap(),
                non_recursive_watch().with_dereference_symlinks(false),
                true,
            )
            .expect("watch dangling symlink");

        let watch = event_loop.watches.get(&link).expect("link watch");
        assert!(!watch.is_dir);
        assert!(!watch.dereference);
    }

    #[test]
    fn watches_record_whether_the_path_is_a_directory() {
        let tmpdir = tempfile::tempdir().unwrap();
        let root = tmpdir.path().to_path_buf();
        let directory = root.join("directory");
        let nested = directory.join("nested");
        let file = root.join("file");
        std::fs::create_dir_all(&nested).unwrap();
        std::fs::write(&file, b"").unwrap();
        let file_link = root.join("file_link");
        let directory_link = root.join("directory_link");
        std::os::unix::fs::symlink(&file, &file_link).unwrap();
        std::os::unix::fs::symlink(&directory, &directory_link).unwrap();

        let mut event_loop = test_event_loop();
        event_loop
            .add_watch(WatchPath::new(&file).unwrap(), non_recursive_watch(), true)
            .unwrap();
        event_loop
            .add_watch(WatchPath::new(&file_link).unwrap(), non_recursive_watch(), true)
            .unwrap();
        event_loop
            .add_watch(
                WatchPath::new(&directory_link).unwrap(),
                non_recursive_watch().with_dereference_symlinks(false),
                true,
            )
            .unwrap();
        event_loop
            .add_watch(WatchPath::new(&directory).unwrap(), recursive_watch(), true)
            .unwrap();

        assert!(!event_loop.watches.get(&file).unwrap().is_dir);
        assert!(!event_loop.watches.get(&file_link).unwrap().is_dir);
        assert!(!event_loop.watches.get(&directory_link).unwrap().is_dir);
        assert!(event_loop.watches.get(&directory).unwrap().is_dir);
        assert!(event_loop.watches.get(&nested).unwrap().is_dir);
    }

    #[test]
    fn a_directory_replaced_by_a_file_before_the_add_is_recorded_as_a_file() {
        let tmpdir = tempfile::tempdir().unwrap();
        let path = tmpdir.path().join("replaced");
        std::fs::write(&path, b"").unwrap();

        let mut event_loop = test_event_loop();
        event_loop
            .add_single_watch(WatchPath::new(&path).unwrap(), false, true, true, true)
            .unwrap();

        assert!(!event_loop.watches.get(&path).unwrap().is_dir);
    }

    #[test]
    fn a_file_replaced_by_a_directory_before_the_add_is_recorded_as_a_directory() {
        let tmpdir = tempfile::tempdir().unwrap();
        let path = tmpdir.path().join("replaced");
        std::fs::create_dir(&path).unwrap();

        let mut event_loop = test_event_loop();
        event_loop
            .add_single_watch(WatchPath::new(&path).unwrap(), false, true, true, false)
            .unwrap();

        assert!(event_loop.watches.get(&path).unwrap().is_dir);
    }

    #[test]
    fn watching_a_dangling_symlink_with_dereference_is_not_found() {
        let tmpdir = tempfile::tempdir().unwrap();
        let link = tmpdir.path().join("link");
        std::os::unix::fs::symlink(tmpdir.path().join("missing"), &link).unwrap();

        let inotify = super::inotify_sys::Inotify::init().unwrap();
        let mut event_loop = EventLoop::new(inotify, Box::new(|_| {}), &Config::default()).unwrap();

        let result =
            event_loop.add_watch(WatchPath::new(&link).unwrap(), non_recursive_watch(), true);

        assert!(matches!(
            result,
            Err(Error {
                paths: _,
                kind: ErrorKind::PathNotFound
            })
        ))
    }

    #[test]
    fn recursive_watch_of_a_symlink_to_a_file_still_follows_it() {
        let tmpdir = tempfile::tempdir().unwrap();
        let destination = tmpdir.path().join("destination");
        let link = tmpdir.path().join("link");
        std::fs::write(&destination, "").unwrap();
        std::os::unix::fs::symlink(&destination, &link).unwrap();

        let inotify = super::inotify_sys::Inotify::init().unwrap();
        let mut event_loop = EventLoop::new(inotify, Box::new(|_| {}), &Config::default()).unwrap();

        event_loop
            .add_watch(WatchPath::new(&link).unwrap(), recursive_watch(), true)
            .expect("watch link recursively");

        let watch = event_loop.watches.get(&link).expect("link watch");
        assert!(watch.dereference);
        assert!(!watch.watch_mask.intersects(super::RESOLUTION_FLAGS));
    }

    #[test]
    fn a_recursive_walk_stops_at_an_explicit_non_dereferenced_link() {
        let tmpdir = tempfile::tempdir().unwrap();
        let outside = tempfile::tempdir().unwrap();
        let root = tmpdir.path().to_path_buf();
        let destination = outside.path().join("destination");
        let nested = destination.join("nested");
        let link = root.join("link");
        std::fs::create_dir_all(&nested).unwrap();
        std::os::unix::fs::symlink(&destination, &link).unwrap();

        let inotify = super::inotify_sys::Inotify::init().unwrap();
        let mut event_loop = EventLoop::new(inotify, Box::new(|_| {}), &Config::default()).unwrap();

        event_loop
            .add_watch(
                WatchPath::new(&link).unwrap(),
                non_recursive_watch().with_dereference_symlinks(false),
                true,
            )
            .expect("watch link");
        event_loop
            .add_watch(WatchPath::new(&root).unwrap(), recursive_watch(), true)
            .expect("watch root recursively");

        let watch = event_loop.watches.get(&link).expect("link watch");
        assert!(!watch.dereference);
        assert!(watch.metadata.is_user_watch);
        assert!(
            !event_loop.watches.contains_key(&link.join("nested")),
            "the recursive walk crossed an explicit non-dereferenced link"
        );
    }

    #[test]
    fn watch_with_dereference_disabled_reports_the_link_not_its_destination() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_data_events();
        let destination = tmpdir.path().join("destination");
        let link = tmpdir.path().join("link");
        std::fs::write(&destination, "").expect("write");
        std::os::unix::fs::symlink(&destination, &link).expect("symlink");

        watcher
            .watcher
            .watch_with(
                &link,
                non_recursive_watch().with_dereference_symlinks(false),
            )
            .expect("watch link");
        watcher.watch_nonrecursively(&destination);

        std::fs::write(&destination, "123").expect("write");

        rx.wait_ordered_exact([expected(&destination).modify_data_any().multiple()]);
    }

    /// Taking a watch off a link must not drop an ancestor's coverage of the destination.
    #[test]
    fn watching_a_link_itself_keeps_the_ancestors_recursive_coverage() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_data_events();
        let destination = tmpdir.path().join("destination");
        std::fs::create_dir(&destination).expect("create");
        let file = destination.join("file");
        std::fs::write(&file, "").expect("write");
        let link = tmpdir.path().join("link");
        std::os::unix::fs::symlink(&destination, &link).expect("symlink");

        watcher.watch_nonrecursively(&link);
        watcher.watch_recursively(tmpdir.path());
        watcher
            .watcher
            .watch_with(
                &link,
                non_recursive_watch().with_dereference_symlinks(false),
            )
            .expect("watch the link itself");

        std::fs::write(&file, "123").expect("write");

        let reported: std::collections::HashSet<_> =
            rx.iter().flat_map(|event| event.paths).collect();
        assert_eq!(
            reported,
            std::collections::HashSet::from([file]),
            "the ancestor recursive watch must keep reporting the destination by its real path"
        );
    }

    /// It does drop it when the link is the only way the tree reaches the destination.
    #[test]
    fn watching_a_link_itself_drops_a_destination_reached_only_through_it() {
        let outside = testdir();
        let destination = outside.path().join("destination");
        let nested = destination.join("nested");
        std::fs::create_dir_all(&nested).expect("create");
        let file = nested.join("file");
        std::fs::write(&file, "").expect("write");

        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_data_events();
        let link = tmpdir.path().join("link");
        std::os::unix::fs::symlink(&destination, &link).expect("symlink");

        watcher.watch_recursively(tmpdir.path());
        watcher
            .watcher
            .watch_with(
                &link,
                non_recursive_watch().with_dereference_symlinks(false),
            )
            .expect("watch the link itself");

        std::fs::write(&file, "123").expect("write");

        let reported: Vec<_> = rx.iter().flat_map(|event| event.paths).collect();
        assert!(
            reported.is_empty(),
            "the destination is still reported after the caller asked not to follow the link: \
             {reported:?}"
        );
    }

    /// Every descriptor's owner count equals the number of paths that hold it.
    fn assert_owner_counts_consistent(event_loop: &EventLoop) {
        let mut expected = std::collections::HashMap::new();
        for watch in event_loop.watches.values() {
            *expected.entry(watch.watch_descriptor.clone()).or_insert(0) += 1;
        }
        assert_eq!(event_loop.watches.owner_counts, expected);
    }

    #[test]
    fn removing_one_owner_of_a_shared_descriptor_keeps_it_for_the_other() {
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let destination = tmpdir.path().join("destination");
        std::fs::create_dir(&destination).expect("create destination");
        let link = tmpdir.path().join("link");
        std::os::unix::fs::symlink(&destination, &link).expect("symlink");

        let (tx, rx) = mpsc::channel();
        let inotify = super::inotify_sys::Inotify::init().expect("inotify");
        let mut event_loop =
            EventLoop::new(inotify, Box::new(tx), &Config::default()).expect("event loop");
        event_loop
            .add_watch(
                WatchPath::new(&destination).unwrap(),
                non_recursive_watch(),
                true,
            )
            .expect("watch destination");
        event_loop
            .add_watch(WatchPath::new(&link).unwrap(), non_recursive_watch(), true)
            .expect("watch link");

        let descriptor = event_loop.watches[&destination].watch_descriptor.clone();
        assert_eq!(
            event_loop.watches[&link].watch_descriptor, descriptor,
            "a dereferenced link to a watched directory shares its inotify descriptor"
        );
        assert_eq!(event_loop.watches.owner_count(&descriptor), 2);
        assert_owner_counts_consistent(&event_loop);

        event_loop
            .remove_watch(destination.clone(), false)
            .expect("unwatch destination");
        assert_eq!(event_loop.watches.owner_count(&descriptor), 1);
        assert_eq!(event_loop.paths.get(&descriptor), Some(&link));
        assert_owner_counts_consistent(&event_loop);

        // The kernel watch must survive and now report through the remaining owner.
        let file = destination.join("file");
        std::fs::write(&file, "123").expect("write");
        event_loop.handle_inotify();
        let reported: Vec<_> = rx
            .try_iter()
            .filter_map(|event: Result<Event>| event.ok())
            .flat_map(|event| event.paths)
            .collect();
        assert!(
            reported.contains(&link.join("file")),
            "the shared descriptor stopped reporting after one owner was removed: {reported:?}"
        );

        event_loop
            .remove_watch(link.clone(), false)
            .expect("unwatch link");
        assert_eq!(event_loop.watches.owner_count(&descriptor), 0);
        assert!(event_loop.paths.is_empty());
        assert_owner_counts_consistent(&event_loop);
        let remove_result = event_loop
            .inotify
            .as_mut()
            .expect("inotify instance")
            .watches()
            .remove(descriptor);
        assert_eq!(
            remove_result.unwrap_err().raw_os_error(),
            Some(libc::EINVAL),
            "removing the last owner must release the kernel watch"
        );
    }

    #[test]
    fn update_paths_batch_adds_then_events_arrive() {
        let tmpdir = testdir();
        let (mut watcher, mut rx) = watcher_with_data_events();
        let directories: Vec<_> = ["a", "b", "c"]
            .iter()
            .map(|name| tmpdir.path().join(name))
            .collect();
        let files: Vec<_> = directories
            .iter()
            .map(|directory| {
                std::fs::create_dir(directory).expect("create dir");
                let file = directory.join("file");
                std::fs::write(&file, "").expect("create file");
                file
            })
            .collect();

        watcher
            .watcher
            .update_paths(
                directories
                    .iter()
                    .map(|directory| crate::PathOp::watch_non_recursive(directory.clone()))
                    .collect(),
            )
            .expect("batch watch");

        for file in &files {
            std::fs::write(file, "123").expect("write");
        }
        rx.wait_unordered_exact(
            files
                .iter()
                .map(|file| expected(file).modify_data_any().multiple()),
        );

        let mut watched: Vec<_> = watcher
            .watcher
            .watched_paths()
            .expect("watched paths")
            .into_iter()
            .map(|(path, _)| path)
            .collect();
        watched.sort();
        assert_eq!(watched, directories);
    }

    #[test]
    fn update_paths_stops_at_the_first_failing_op_like_the_default() {
        let tmpdir = testdir();
        let (mut watcher, _rx) = watcher_with_data_events();
        let first = tmpdir.path().join("first");
        let last = tmpdir.path().join("last");
        let missing = tmpdir.path().join("missing");
        std::fs::create_dir(&first).expect("create");
        std::fs::create_dir(&last).expect("create");
        watcher.watch_nonrecursively(&first);
        watcher.watch_nonrecursively(&last);

        let error = watcher
            .watcher
            .update_paths(vec![
                crate::PathOp::unwatch(first.clone()),
                crate::PathOp::watch_non_recursive(missing.clone()),
                crate::PathOp::unwatch(last.clone()),
            ])
            .expect_err("watching a missing path fails");

        assert!(matches!(error.source.kind, ErrorKind::PathNotFound));
        assert!(
            matches!(&error.origin, Some(crate::PathOp::Watch(path, _)) if path == &missing),
            "origin: {:?}",
            error.origin
        );
        assert_eq!(error.remaining.len(), 1);
        assert!(matches!(&error.remaining[0], crate::PathOp::Unwatch(path) if path == &last));

        let watched: Vec<_> = watcher
            .watcher
            .watched_paths()
            .expect("watched paths")
            .into_iter()
            .map(|(path, _)| path)
            .collect();
        assert_eq!(
            watched,
            vec![last],
            "ops before the failure ran, ops after it did not"
        );
    }

    #[test]
    fn tearing_down_many_watches_releases_every_descriptor() {
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let directories: Vec<_> = (0..500)
            .map(|index| {
                let directory = tmpdir.path().join(format!("dir-{index}"));
                std::fs::create_dir(&directory).expect("create dir");
                directory
            })
            .collect();

        let mut event_loop = test_event_loop();
        event_loop
            .update_paths(
                directories
                    .iter()
                    .map(|directory| crate::PathOp::watch_non_recursive(directory.clone()))
                    .map(super::ResolvedPathOp::new)
                    .collect(),
            )
            .expect("batch watch");
        assert_eq!(event_loop.watches.len(), directories.len());
        assert_eq!(event_loop.paths.len(), directories.len());
        assert_owner_counts_consistent(&event_loop);
        let descriptors: Vec<_> = event_loop
            .watches
            .values()
            .map(|watch| watch.watch_descriptor.clone())
            .collect();

        // Remove half one at a time and half as a batch, so both paths are covered.
        let (single, batched) = directories.split_at(directories.len() / 2);
        for directory in single {
            event_loop
                .remove_watch(directory.clone(), false)
                .expect("unwatch");
        }
        assert_owner_counts_consistent(&event_loop);
        event_loop
            .update_paths(
                batched
                    .iter()
                    .map(|directory| crate::PathOp::unwatch(directory.clone()))
                    .map(super::ResolvedPathOp::new)
                    .collect(),
            )
            .expect("batch unwatch");

        assert!(event_loop.watches.is_empty());
        assert!(event_loop.watches.owner_counts.is_empty());
        assert!(event_loop.paths.is_empty());
        let mut inotify_watches = event_loop.inotify.as_mut().expect("inotify").watches();
        for descriptor in descriptors {
            assert_eq!(
                inotify_watches.remove(descriptor).unwrap_err().raw_os_error(),
                Some(libc::EINVAL),
                "every kernel watch must have been released"
            );
        }
    }

    /// Times adding and removing many non-recursive watches through `watch`/`unwatch` one at a
    /// time and through one `update_paths` batch each way. Ignored by default; run with
    /// `cargo test -p notify --lib --release bench_non_recursive_watch_churn -- --ignored --nocapture`.
    /// `NOTIFY_BENCH_WATCHES` overrides the count (default 10000).
    #[test]
    #[ignore = "benchmark"]
    fn bench_non_recursive_watch_churn() {
        let count: usize = std::env::var("NOTIFY_BENCH_WATCHES")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(10_000);
        let tmpdir = tempfile::tempdir().expect("tmpdir");
        let directories: Vec<_> = (0..count)
            .map(|index| {
                let directory = tmpdir.path().join(format!("dir-{index}"));
                std::fs::create_dir(&directory).expect("create dir");
                directory
            })
            .collect();

        let mut watcher = INotifyWatcher::new(|_| {}, Config::default()).expect("watcher");
        let start = std::time::Instant::now();
        for directory in &directories {
            watcher
                .watch(directory, RecursiveMode::NonRecursive)
                .expect("watch");
        }
        let single_add = start.elapsed();
        let start = std::time::Instant::now();
        for directory in &directories {
            watcher.unwatch(directory).expect("unwatch");
        }
        let single_remove = start.elapsed();

        let start = std::time::Instant::now();
        watcher
            .update_paths(
                directories
                    .iter()
                    .map(|directory| crate::PathOp::watch_non_recursive(directory.clone()))
                    .collect(),
            )
            .expect("batch watch");
        let batched_add = start.elapsed();
        let start = std::time::Instant::now();
        watcher
            .update_paths(
                directories
                    .iter()
                    .map(|directory| crate::PathOp::unwatch(directory.clone()))
                    .collect(),
            )
            .expect("batch unwatch");
        let batched_remove = start.elapsed();

        println!(
            "{count} non-recursive watches: single add {single_add:?}, single remove \
             {single_remove:?}, batched add {batched_add:?}, batched remove {batched_remove:?}"
        );
    }
}
