//! This crate defines some tools that help writing tests to detect
//! memory errors in Rust code that either uses, or depends on,
//! untrustworthy `unsafe` code.
//!
//! The main struct defined in the crate is `MemDebug`, which provides
//! some tools to track its allocation status.
//!
//! The main mechanics to test double drop and use after free bugs
//! are just to create some `MemDebug` objects, and feed them in
//! whatever algorithm one wants to test. `MemDebug` objects will make the
//! test function panic upon detecting those bugs.
//!
//! The main mechanics to test memory leaks are tags. One can tag existing
//! `MemDebug` instances, and then query to see if some assertions hold at
//! any point in time about the set of `MemDebug` objects with the given tag.
//!
//! For example, if one creates some `MemDebug` objects, tags them with tag
//! `x`, and then uses them to create a collection that uses untrustworthy
//! unsafe code to manage the memory at low level, memory leaks can be tested
//! by making sure that
//! "the set of `MemDebug` instances with tag `x` is empty".

mod tag_and_id;
pub use tag_and_id::{Id, IntoIdIter, IntoTagIter, Tag};

mod alloc_tracker;
pub(crate) use alloc_tracker::AllocationTracker;
pub use alloc_tracker::{ReadOnlyMutexGuard, TagsByIdRegister, TagsRegister};

mod mem_debug;
pub use mem_debug::MemDebug;

#[cfg(test)]
mod test;
