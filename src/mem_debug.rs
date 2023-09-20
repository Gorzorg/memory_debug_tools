use std::cell::UnsafeCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Mutex;

use super::{
    AllocationTracker, Id, IntoIdIter, IntoTagIter, ReadOnlyMutexGuard, Tag, TagsByIdRegister,
    TagsRegister,
};

/// This variable is to be used whenever a `MemDebug` object is created or cloned
/// It is a counter that is increased by 1 ad every new `MemDebug` instance.
static MEM_DEBUG_ID: Mutex<Id> = Mutex::new(Id::const_from(0));

/// This variable is to be used whenever a `Tag` object is created
/// with `MemDebug::new_tag`.
static TAG_ID: Mutex<Tag> = Mutex::new(Tag::const_from(0));

/// This is the register that keeps track of which `MemDebug` objects are allocated,
/// and that manages the tags given to them.
///
/// Most of the methods of `MemDebug` just forward calls to methods of
/// `MEM_DEBUG_ALLOCATIONS_TRACKER`, i.e. methods of `AllocationTracker`
/// where `&self` is a globally defined instance.
static MEM_DEBUG_ALLOCATIONS_TRACKER: AllocationTracker = AllocationTracker::const_default();

/// This struct can be used to detect memory errors such as:
///     - use after free
///     - double drop
///     - use of uninitialized memory
///     - memory leaks
///
/// It can also potentially be used to track the origin and trajectory
/// of objects in the program, but this is not the main intended use case.
///
/// It is intended for use in test functions only.
///
/// ## Explanation
///
/// It works as follows:
/// Every new `MemDebug` instance is given a new globally unique id.
/// This id is tracked in a global register.
/// When the `MemDebug` object is dropped, the id is deleted from
/// the global register.
///
/// ## What about `Clone` ?
///
/// Clones of `MemDebug` instances are treated as brand new instances,
/// and receive their own unique id. Keep this in mind when structuring
/// your tests.
///
/// ## Tags
///
/// For some use cases, it comes handy to tag instances of `MemDebug`.
/// Every instance can have an arbitrary number of tags attached,
/// and every tag can tag arbitrarily many instances.
///
/// Tags are also stored in a global register, that can be queried
/// in order to assert conditions.
#[derive(Debug)]
pub struct MemDebug<Data = ()> {
    pub(crate) id: Id,
    data: std::mem::ManuallyDrop<Data>,
}

impl<Data> std::ops::Drop for MemDebug<Data> {
    #[inline]
    fn drop(&mut self) {
        match MEM_DEBUG_ALLOCATIONS_TRACKER.remove_alloc_record(self) {
            Ok(()) => unsafe {
                // Safety: we only call the drop if `remove_alloc_record` has
                // returned `Ok`, which means only if `self.id` is registered
                // as alive in the global register.
                //
                // Any malfunction of this assumption can be traced back to
                // either a malfunction of the global register, or to the
                // use of unsafe code that purposefully creates invalid
                // `MemDebug` instances.
                core::mem::ManuallyDrop::drop(&mut self.data)
            },
            Err(()) => panic!("Attepted dropping a `MemDebug` instance that is either uninitialized, or has already been dropped."),
        }
    }
}

impl<Data: Clone> Clone for MemDebug<Data> {
    #[inline]
    fn clone(&self) -> Self {
        let out = Self::new((*self.data).clone(), std::iter::empty());
        let tags = MEM_DEBUG_ALLOCATIONS_TRACKER
            .get_tags_by_id()
            .get(&self.id)
            .map(|s| s.lock().unwrap().clone())
            .unwrap_or_default();
        MEM_DEBUG_ALLOCATIONS_TRACKER.add_tags(
            out.id,
            tags,
        ).expect("This is a bug: earlier in this function, we need to dereference `self`. This means that, if `self` is invalid, the function crashes before reaching this point. On the other hand, is `self` is valid, also `out` is valid, which means that the return value of this function should not be `Err(())`");
        out
    }
}

impl<Data: Default> Default for MemDebug<Data> {
    #[inline]
    fn default() -> Self {
        Self::new(Data::default(), std::iter::empty())
    }
}

impl<Data> core::ops::Deref for MemDebug<Data> {
    type Target = Data;
    #[inline]
    fn deref(&self) -> &Self::Target {
        // We make sure that the instance we are dereferencing is valid.
        // If the instance is not valid, a panic is triggered.
        MemDebug::deref_assert_alive(self.id);
        &self.data
    }
}

impl<Data> core::ops::DerefMut for MemDebug<Data> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        // We make sure that the instance we are dereferencing is valid.
        // If the instance is not valid, a panic is triggered.
        MemDebug::deref_assert_alive(self.id);
        &mut self.data
    }
}

impl<Data> MemDebug<Data> {
    /// ## Caution
    ///
    /// Creating any `MemDebug` object directly with this method **will** break
    /// the invariants of `MEM_DEBUG_ALLOCATIONS_TRACKER`, unless it is used
    /// in conjunction with other low level memory management devices such as
    /// `core::mem::ManuallyDrop`.
    ///
    /// Breaking the invariants of `MEM_DEBUG_ALLOCATIONS_TRACKER` may cause the program
    /// to panic, and to warn the user about nonexistent memory error bugs.
    #[inline]
    pub unsafe fn from_raw_parts(id: Id, data: Data) -> Self {
        Self {
            id,
            data: core::mem::ManuallyDrop::new(data),
        }
    }

    /// Given an instance of `Box<Data>`, create a `MemDebug<Data> instance with it.
    ///
    /// Basically the same as `MemDebug::new`, with data that already lives in a `Box`.
    ///
    /// There are two main use cases for this:
    /// - when `Data` is not statically sized, it is impossible to give `Data` arguments
    ///   to functions, which implies that `MemDebug::new` is not suitable for unsized
    ///   `Data`.
    /// - when one is given data that has already been boxed, it is a waste of computation
    ///   to un-box and re-box it.
    #[inline]
    pub fn new<I: IntoIterator<Item = Tag>>(data: Data, tags: I) -> Self {
        let mut counter = MEM_DEBUG_ID.lock().unwrap();
        **counter += 1;
        let s = unsafe { Self::from_raw_parts(*counter, data) };
        MEM_DEBUG_ALLOCATIONS_TRACKER.add_alloc_record(&s, tags);
        s
    }

    /// Turns `self` into its boxed data. All references to the id
    /// of `self` are dropped from the global register.
    ///
    /// Closely mimics the code executed when dropping `MemDebug` instances,
    /// with the difference that the data is returned instead of dropped.
    #[inline]
    pub fn into_inner(self) -> Data {
        match MEM_DEBUG_ALLOCATIONS_TRACKER.remove_alloc_record(&self) {
            Ok(()) => {
                let md = core::mem::ManuallyDrop::new(self);
                unsafe {
                    // Safety: we are copying the data, but we will immediately after
                    // forget the original copy without executing its drop method.
                    //
                    // The net effect is that we are only moving `data` out of `self`
                    core::ptr::read((&md.data) as *const _ as *const _)
                }
            },
            Err(()) => panic!("Attempted reading from a `MemDebug` instance that is either uninitialized, or has already been dropped."),
        }
    }

    /// Every `MemDebug` instance can keep track of its memory address over time.
    /// This tracking is not automatic, since there is no way to trigger logic
    /// automatically when an object is moved.
    ///
    /// The addresses are tracked in a centralized register, that is indexed over
    /// the `id` of `MemDebug` instances. The entries of the register can be
    /// updated by using the `MemDebug::update_address` method.
    ///
    /// `MemDebug::has_been_moved` returns `true` if and only if the current
    /// address of the instance is different from the address that was last
    /// recorded by calling `update_address` on a `MemDebug` instance with
    /// the same `id`.
    /// In case the address was never updated, the address of the object at creation
    /// time is in the register, and is used as comparison with the current address.
    #[inline]
    pub fn has_been_moved(&self) -> bool {
        MEM_DEBUG_ALLOCATIONS_TRACKER.has_been_moved(self)
    }

    /// Every `MemDebug` instance can keep track of its memory address over time.
    /// This tracking is not automatic, since there is no way to trigger logic
    /// automatically when an object is moved.
    ///
    /// The addresses are tracked in a centralized register, that is indexed over
    /// the `id` of `MemDebug` instances. The entries of the register can be
    /// updated by using this method. It updates the register entry that
    /// corresponds to `self.id` to the current memory address of `self`.
    #[inline]
    pub fn update_address(&mut self) {
        MEM_DEBUG_ALLOCATIONS_TRACKER.update_address(self)
    }

    /// Getter method that returns a copy of `self.id`.
    #[inline]
    pub fn id(&self) -> Id {
        self.id
    }

    /// Method that returns the memory address of `self` in standardized form.
    #[inline]
    pub fn as_ptr(&self) -> *const MemDebug<()> {
        self as *const _ as _
    }
}

// These methods only handle `Id` and `Tag` values, without requiring
// `self` references in the code.
//
// This would make it ambiguous to call them if they were implemented for
// `MemDebug<Data>` for more than one value of `Data`.
//
// Therefore, implementing them only for `MemDebug<()>` allows the user
// to simply write `MemDebug::method` instead of
// `MemDebug::<SomeArbitraryType>::method`
// when calling them.
impl MemDebug {
    #[inline]
    pub fn create_tag() -> Tag {
        let mut tag = TAG_ID.lock().unwrap();
        **tag += 1;
        *tag
    }

    #[inline]
    pub fn create_tags(how_many: usize) -> Vec<Tag> {
        let mut tag = TAG_ID.lock().unwrap();
        let mut out = vec![];
        out.reserve(how_many);
        for _ in 0..how_many {
            **tag += 1;
            out.push(*tag);
        }
        out
    }

    #[inline]
    pub fn add_tags<I: IntoTagIter>(id: Id, tags: I) -> Result<(), ()> {
        MEM_DEBUG_ALLOCATIONS_TRACKER.add_tags(id, tags.into_tag_iter())
    }

    #[inline]
    pub fn remove_tags<I: IntoTagIter>(id: Id, tags: I) {
        MEM_DEBUG_ALLOCATIONS_TRACKER.remove_tags(id, tags.into_tag_iter());
    }

    #[inline]
    pub fn add_tag_to_group<J: IntoIdIter>(group: J, tag: Tag) -> Result<(), BTreeSet<Id>> {
        MEM_DEBUG_ALLOCATIONS_TRACKER.add_tag_to_group(group.into_id_iter(), tag)
    }

    #[inline]
    pub fn remove_tag_from_group<J: IntoIdIter>(group: J, tag: Tag) {
        MEM_DEBUG_ALLOCATIONS_TRACKER.remove_tag_from_group(group.into_id_iter(), tag)
    }

    #[inline]
    pub fn assert_on_alloc<F: FnOnce(&BTreeMap<Id, *const MemDebug<()>>) -> bool>(func: F) -> bool {
        MEM_DEBUG_ALLOCATIONS_TRACKER.assert_on_alloc(func)
    }

    /// Returns `true` if `id` is still marked as not dropped in the global register.
    /// This is a particular case of `MemDebug::assert_on_alloc`
    #[inline]
    pub fn is_alive(id: Id) -> bool {
        Self::assert_on_alloc(|m| m.contains_key(&id))
    }

    /// This function is only used in the implementation of `Deref` and `DerefMut`
    /// for `MemDebug`. This function only asserts that the instance of
    /// `MemDebug` one is about to dereference corresponds actually
    /// initialized memory that has not been dropped yet.
    #[inline]
    fn deref_assert_alive(id: Id) {
        assert!(
            MEM_DEBUG_ALLOCATIONS_TRACKER.assert_on_alloc(|m| m.contains_key(&id)),
            "Attempted using a `MemDebug` instance that corresponds to uninitialized, or already dropped, memory."
        );
    }

    /// Read-only mutex guard to the `BTreeSet<Id>` value that
    /// corresponds to the `tag` key in the `Tag -> BTreeSet<Id>` global map.
    ///
    /// ## Warning:
    ///
    /// Until the guard is in scope, any access to the same entry in the
    /// map from other threads will be blocked. Therefore, we recommend using
    /// this method only when necessary.
    #[inline]
    pub fn get_tag<'a>(tag: Tag) -> ReadOnlyMutexGuard<'a, BTreeSet<Id>> {
        MEM_DEBUG_ALLOCATIONS_TRACKER.get_tag(tag)
    }

    /// Read-only mutex guard to the `BTreeSet<Tag>` value that
    /// corresponds to the `id` key in the `Id -> BTreeSet<Tag>` global map.
    ///
    /// ## Warning:
    ///
    /// Until the guard is in scope, any access to the same entry in the
    /// map from other threads will be blocked. Therefore, we recommend using
    /// this method only when necessary.
    #[inline]
    pub fn get_tags_on_id<'a>(id: Id) -> ReadOnlyMutexGuard<'a, BTreeSet<Tag>> {
        MEM_DEBUG_ALLOCATIONS_TRACKER.get_tags_on_id(id)
    }

    /// Read-only mutex guard to the `Tag -> BTreeSet<Id>` global map.
    ///
    /// ## Warning:
    ///
    /// Until the guard is in scope, any access to the tags map from other
    /// threads will be blocked. Therefore, we recommend using this method
    /// only when necessary.
    ///
    /// To verify logical conditions on single `Tag` values, one can use
    /// `MemDebug::get_tag`, which only locks one entry of the map, leaving
    /// the rest free for use by other threads.
    #[inline]
    pub fn get_tags<'a>() -> ReadOnlyMutexGuard<'a, UnsafeCell<TagsRegister>> {
        MEM_DEBUG_ALLOCATIONS_TRACKER.get_tags()
    }

    /// Read-only mutex guard to the `Id -> BTreeSet<Tag>` global map.
    ///
    /// ## Warning:
    ///
    /// Until the guard is in scope, any access to the tags map from other
    /// threads will be blocked. Therefore, we recommend using this method
    /// only when necessary.
    ///
    /// To verify logical conditions on the tags applied to a single `Id`,
    /// one can use `MemDebug::get_tags_on_id`, which only locks one entry
    /// of the map, leaving the rest free for use by other threads.
    #[inline]
    pub fn get_tags_by_id<'a>() -> ReadOnlyMutexGuard<'a, UnsafeCell<TagsByIdRegister>> {
        MEM_DEBUG_ALLOCATIONS_TRACKER.get_tags_by_id()
    }
}
