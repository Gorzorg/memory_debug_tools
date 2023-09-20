use super::{Id, MemDebug, Tag};
use core::cell::UnsafeCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Mutex, MutexGuard};

/// Utility struct whose purpose is to perform as a `MutexGuard`,
/// without implementing the `DerefMut` trait. Essentially, it
/// guarantees exclusive access to the data guarded by the mutex,
/// in read only mode.
///
/// This struct is only returned by calls to `AllocationTracker`
/// methods.
///
/// ## Rationale
///
/// An `RwLock` could have been used instead of this, but Rust
/// makes no guarantees on the priority police implemented by
/// `RwLock`. Therefore, considering that this crate only implements
/// testing tools, and considering performance as a second priority,
/// in order to make reasoning about the code implemented by
/// `AllocationTracker` easier, we stick with using `Mutex` everywhere,
/// even when we need read-only guards.
#[repr(transparent)]
pub struct ReadOnlyMutexGuard<'a, Data>(MutexGuard<'a, Data>);

impl<'a, Data> core::ops::Deref for ReadOnlyMutexGuard<'a, UnsafeCell<Data>> {
    type Target = Data;
    fn deref(&self) -> &Self::Target {
        // Safety: self contains a `MutexGuard`, which implies that other
        // threads do not have references to the contained data.
        unsafe { &*self.0.get() }
    }
}

impl<'a, Data> core::ops::Deref for ReadOnlyMutexGuard<'a, BTreeSet<Data>> {
    type Target = BTreeSet<Data>;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

impl<'a, Key, Value> core::ops::Deref for ReadOnlyMutexGuard<'a, BTreeMap<Key, Value>> {
    type Target = BTreeMap<Key, Value>;
    fn deref(&self) -> &Self::Target {
        &*self.0
    }
}

/// Global register that tracks `MemDebug` objects.
/// It serves mainly the purposes of
/// - tracking which objects are allocated
/// - detecting if objects heve been moved
/// - detecting double drop bugs
/// - detecting use after drop bugs
/// - detecting memory leaks
///
/// It does so by keeping a register of when `MemDebug`
/// objects are allocated, and of when they are deallocated.
///
/// Also, it allows to tag objects, and to query which objects
/// have which tags at any moment in time.
///
/// Every `MemDebug` object has a unique id, and `MemDebug` does
/// not implement `Copy`. This makes it possible to query the
/// `AllocationTracker` about existing `MemDebug` instances
/// by referring to their id.
///
/// ## Detecting memory leaks
///
/// If a `MemDebug` object should not outlive some scope, then
/// a way to detect if that object is part of a memory leak is to
/// save its id somewhere, and then query the `AllocationTracker`
/// about the existence of that id in its registry.
///
/// ## Detecting moves
///
/// Detecting object moves is done by keeping a pointer stored
/// in correspondence of any `MemDebug` id that corresponds to
/// an allocated instance.
/// The pointer does not have to be up to date, but functionality
/// is provided to update the location recorded for the object.
/// If the memory location of a `MemDebug` object is different from
/// the last location updated in `AllocationTracker`, this proves that
/// the object has been moved at least once.
/// Conversely, if the memory addresses coincide, that means that
/// most likely the object has not been moved since the last address update.
#[derive(Default)]
pub(crate) struct AllocationTracker {
    allocs: Mutex<BTreeMap<Id, *const MemDebug>>,
    tags: Mutex<UnsafeCell<TagsRegister>>,
    tags_by_id: Mutex<UnsafeCell<TagsByIdRegister>>,
}

pub type TagsRegister = BTreeMap<Tag, Box<Mutex<BTreeSet<Id>>>>;
pub type TagsByIdRegister = BTreeMap<Id, Box<Mutex<BTreeSet<Tag>>>>;

macro_rules! get_alloc_tracker_locks {
    ([$tracker: expr][][$($tags_expr: expr)?][$($tags_by_id_expr: expr)?] allocs $($tok: ident)*) => {
        get_alloc_tracker_locks!(
            [$tracker]
            [$tracker.allocs.lock().unwrap()]
            [$($tags_expr)?]
            [$($tags_by_id_expr)?]
            $($tok)*
        )
    };
    ([$tracker: expr][$($alloc_expr: expr)?][][$($tags_by_id_expr: expr)?] tags $($tok: ident)*) => {
        get_alloc_tracker_locks!(
            [$tracker]
            [$($alloc_expr)?]
            [$tracker.tags.lock().unwrap()]
            [$($tags_by_id_expr)?]
            $($tok)*
        )
    };
    ([$tracker: expr][$($alloc_expr: expr)?][$($tags_expr: expr)?][] tags_by_id $($tok: ident)*) => {
        get_alloc_tracker_locks!(
            [$tracker]
            [$($alloc_expr)?]
            [$($tags_expr)?]
            [$tracker.tags_by_id.lock().unwrap()]
            $($tok)*
        )
    };
    ([$tracker: expr][$($alloc_expr: expr)?][$($tags_expr: expr)?][$($tags_by_id_expr: expr)?]) => {
        (
            $($alloc_expr,)?
            $($tags_expr,)?
            $($tags_by_id_expr,)?
        )
    };
    ($tracker: expr, $($tok: ident)+) => {
        get_alloc_tracker_locks!([$tracker][][][] $($tok)+)
    };

}

impl AllocationTracker {
    #[inline]
    pub(crate) const fn const_default() -> Self {
        Self {
            allocs: Mutex::new(BTreeMap::new()),
            tags: Mutex::new(UnsafeCell::new(BTreeMap::new())),
            tags_by_id: Mutex::new(UnsafeCell::new(BTreeMap::new())),
        }
    }

    #[inline]
    pub(crate) fn add_alloc_record<Data, I: IntoIterator<Item = Tag>>(
        &self,
        object: &MemDebug<Data>,
        tags: I,
    ) {
        let (mut allocs, mut tags_lock, mut tags_by_id_lock) =
            get_alloc_tracker_locks!(self, allocs tags tags_by_id);

        allocs.insert(object.id, object.as_ptr());

        let mut tags_to_object = tags_by_id_lock
            .get_mut()
            .entry(object.id)
            .or_default()
            .lock()
            .unwrap();

        let tags_map = tags_lock.get_mut();

        for t in tags {
            tags_map
                .entry(t)
                .or_default()
                .lock()
                .unwrap()
                .insert(object.id);
            tags_to_object.insert(t);
        }
    }

    pub(crate) fn remove_alloc_record<Data>(&self, object: &MemDebug<Data>) -> Result<(), ()> {
        let (mut allocs, mut tags_lock, mut tags_by_id_lock) =
            get_alloc_tracker_locks!(self, allocs tags tags_by_id);
        if let Some(tags) = tags_by_id_lock.get_mut().remove(&object.id) {
            let tags_map = tags_lock.get_mut();

            for t in tags.lock().unwrap().iter() {
                tags_map
                    .get_mut(&t)
                    .expect("self.tags and self.tags_by_id should be in sync")
                    .lock()
                    .unwrap()
                    .remove(&object.id);
            }
        }
        allocs.remove(&object.id).map(|_| ()).ok_or(())

        // One would be tempted to directly panic here in case of an error,
        // however, we need to actually forward the information about the error
        // to the destructor of `MemDebug`, which will decide to drop, or not
        // to drop, the data, based on that information.
        //
        // This prevents some "panic while panicking" situations.
    }

    #[inline]
    pub(crate) fn update_address<Data>(&self, object: &MemDebug<Data>) {
        let object_is_alive = {
            get_alloc_tracker_locks!(self, allocs)
                .0
                .get_mut(&object.id)
                .map(|addr| *addr = object.as_ptr())
                .is_some()
        };
        // Poisoning: the assert must be executed after the mutex guards have been dropped.
        assert!(
            object_is_alive,
            "Attempted changing the registered memory address of uninitialized, or already dropped, MemDebug instance."
        );
    }

    #[inline]
    pub(crate) fn has_been_moved<Data>(&self, object: &MemDebug<Data>) -> bool {
        let output = {
            get_alloc_tracker_locks!(self, allocs)
                .0
                .get(&object.id)
                .map(|addr_ref| *addr_ref)
        };

        // Poisoning: the assert must be executed after the mutex guards have been dropped.
        assert!(
            output.is_some(),
            "Attempted reading the memory address of uninitialized, or already dropped, MemDebug instance."
        );
        output.unwrap() != object.as_ptr()
    }

    #[inline]
    pub(crate) fn add_tags<I: IntoIterator<Item = Tag>>(&self, id: Id, tags: I) -> Result<(), ()> {
        let (allocs, mut tags_lock, mut tags_by_id_lock) =
            get_alloc_tracker_locks!(self, allocs tags tags_by_id);
        if allocs.contains_key(&id) {
            let mut tags_by_id = tags_by_id_lock
                .get_mut()
                .entry(id)
                .or_default()
                .lock()
                .unwrap();

            let tags_map = tags_lock.get_mut();

            for t in tags {
                tags_map.entry(t).or_default().lock().unwrap().insert(id);
                tags_by_id.insert(t);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    #[inline]
    pub(crate) fn remove_tags<I: IntoIterator<Item = Tag>>(&self, id: Id, tags: I) {
        let (mut tags_lock, mut tags_by_id_lock) = get_alloc_tracker_locks!(self, tags tags_by_id);

        let mut tags_by_id = tags_by_id_lock
            .get_mut()
            .entry(id)
            .or_default()
            .lock()
            .unwrap();

        let tags_map = tags_lock.get_mut();

        for t in tags {
            if tags_by_id.remove(&t) {
                tags_map.get_mut(&t)
                .expect("The data stored in `alloc_tags` and the data stored in `tags_by_id` is synchronized.")
                .lock()
                .unwrap()
                .remove(&id);
            }
            // Since `alloc_tags` and `tags_by_id` keep synchronized data
            // there is no need to do
            // `alloc_tags.get_mut(&t).map(|s| s.remove(&id))`
            // when `tags_by_id.remove(&t) == false`
        }
    }

    #[inline]
    pub(crate) fn add_tag_to_group<J: IntoIterator<Item = Id>>(
        &self,
        group: J,
        tag: Tag,
    ) -> Result<(), BTreeSet<Id>> {
        let (allocs, mut tags_lock, mut tags_by_id_lock) =
            get_alloc_tracker_locks!(self, allocs tags tags_by_id);

        let mut tags = tags_lock.get_mut().entry(tag).or_default().lock().unwrap();

        let tags_by_id = tags_by_id_lock.get_mut();

        let mut bad_id = BTreeSet::new();
        for id in group {
            if allocs.contains_key(&id) {
                tags.insert(id);
                tags_by_id
                    .entry(id)
                    .or_default()
                    .lock()
                    .unwrap()
                    .insert(tag);
            } else {
                bad_id.insert(id);
            }
        }
        if bad_id.is_empty() {
            Ok(())
        } else {
            Err(bad_id)
        }
    }

    #[inline]
    pub(crate) fn remove_tag_from_group<J>(&self, group: J, tag: Tag)
    where
        J: IntoIterator<Item = Id>,
    {
        let (mut tags_lock, mut tags_by_id_lock) = get_alloc_tracker_locks!(self, tags tags_by_id);
        let mut tags = tags_lock.get_mut().entry(tag).or_default().lock().unwrap();

        let tags_by_id = tags_by_id_lock.get_mut();

        for id in group {
            if tags.remove(&id) {
                tags_by_id.get_mut(&id)
                .expect("The data stored in `alloc_tags` and the data stored in `tags_by_id` is synchronized.")
                .lock()
                .unwrap()
                .remove(&tag);
            }
            // Since `alloc_tags` and `tags_by_id` keep synchronized data
            // there is no need to do
            // `alloc_tags.get_mut(&t).map(|s| s.remove(&id))`
            // when `tags_by_id.remove(&t) == false`
        }
    }

    #[inline]
    pub(crate) fn get_tag(&self, tag: Tag) -> ReadOnlyMutexGuard<BTreeSet<Id>> {
        let tags_lock = get_alloc_tracker_locks!(self, tags).0;
        ReadOnlyMutexGuard(
            // Safety: We cannot use `UnsafeCell::get_mut` here because
            // otherwise the borrow-checker complains.
            //
            // What we are doing here is:
            //  - We acquire a reference to the map, which needs to be mutable in
            //    case we need to insert the default value for a key.
            //  - We obtain a `MutexGuard` of one of the entries, we wrap it in
            //    a `ReadOnlyMutexGuard`, and we return it
            //
            // Even though we are returning a reference to data that is technically
            // owned by `self.tags`, and even though `self.tags` might be
            // modified mutably while the returned reference is still alive,
            // this is safe because
            //  - The data being read is behind a `MutexGuard`, so other threads
            //    cannot modify the data while the reference is alive.
            //  - Even if `self.tags` is mutably modified, and the entry that
            //    corresponds to the `tag` key is moved, the returned guard
            //    still remains valid, because the values of the map are
            //    wrapped in a `Box`, which in essence is a pointer. It follows
            //    that, even if the `Box` is moved, the `Mutex` pointed by it
            //    remains fixed in memory, and the `MutexGuard` remains valid.
            unsafe { &mut *tags_lock.get() }
                .entry(tag)
                .or_default()
                .lock()
                .unwrap(),
        )
    }

    #[inline]
    pub fn get_tags_on_id(&self, id: Id) -> ReadOnlyMutexGuard<BTreeSet<Tag>> {
        let tags_by_id_lock = get_alloc_tracker_locks!(self, tags_by_id).0;
        ReadOnlyMutexGuard(
            // Safety: read the safety comment in
            // `MemDebug::get_tag`
            unsafe { &mut *tags_by_id_lock.get() }
                .entry(id)
                .or_default()
                .lock()
                .unwrap(),
        )
    }

    #[inline]
    pub(crate) fn assert_on_alloc<F: FnOnce(&BTreeMap<Id, *const MemDebug<()>>) -> bool>(
        &self,
        func: F,
    ) -> bool {
        func(&*get_alloc_tracker_locks!(self, allocs).0)
    }

    /// for safety demo of the concept, see
    /// [here](https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=3c62db3a4650cd2f2d6a48f04365fe64)
    #[inline]
    pub(crate) fn get_tags(&self) -> ReadOnlyMutexGuard<UnsafeCell<TagsRegister>> {
        ReadOnlyMutexGuard(get_alloc_tracker_locks!(self, tags).0)
    }

    #[inline]
    pub(crate) fn get_tags_by_id(&self) -> ReadOnlyMutexGuard<UnsafeCell<TagsByIdRegister>> {
        ReadOnlyMutexGuard(get_alloc_tracker_locks!(self, tags_by_id).0)
    }
}

// `AllocationTracker` values never own, dereference, or share with the
// outside world, the pointers that they contain.
// Therefore, even if the pointers are invalidated or aliased, sending
// an `AllocationTracker` to another thread cannot cause memory issues.
unsafe impl Send for AllocationTracker {}

// For the same reasons that justify the implementation of `Send`,
// plus the observation that `AllocationTracker` does not
// implement any form of inner mutability, sharing a `&AllocationTracker` value
// does not introduce memory issues, which justifies implementing `Sync`.
unsafe impl Sync for AllocationTracker {}
