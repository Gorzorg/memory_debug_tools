//! Defines the `Tag` and `Id` structs.
//! Those are at the time being just wrappers of `u64`.
//! They are not defined as simple type aliases, so that the compiler
//! can properly warn someone that is trying to use one
//! in place of the other.

#[repr(transparent)]
#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Tag(u64);

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Id(u64);

impl core::ops::Deref for Tag {
    type Target = u64;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl core::ops::DerefMut for Tag {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl core::ops::Deref for Id {
    type Target = u64;
    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl core::ops::DerefMut for Id {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<u64> for Id {
    #[inline]
    fn from(value: u64) -> Self {
        Self(value)
    }
}

impl Tag {
    #[inline]
    pub const fn const_from(value: u64) -> Self {
        Self(value)
    }
}

impl Id {
    #[inline]
    pub const fn const_from(value: u64) -> Self {
        Self(value)
    }
}

/// Something that is IntoIterator, with `Item = Id`,
/// or `Item = &Id`, or `Item = &MemDebug`.
pub trait IntoIdIter: IntoIterator {
    type Iter: Iterator<Item = Id>;
    fn into_id_iter(self) -> Self::Iter;
}

/// Something that is IntoIterator, with `Item = Tag`,
/// or `Item = &Tag`
pub trait IntoTagIter: IntoIterator {
    type Iter: Iterator<Item = Tag>;
    fn into_tag_iter(self) -> Self::Iter;
}

impl<I> IntoIdIter for I
where
    I: IntoIterator,
    (Self, <Self as IntoIterator>::Item): IdIterInner<OuterSelf = Self>,
{
    type Iter = <(Self, <Self as IntoIterator>::Item) as IdIterInner>::Iter;
    fn into_id_iter(self) -> Self::Iter {
        <(Self, <Self as IntoIterator>::Item) as IdIterInner>::into_iter(self)
    }
}

impl<I> IntoTagIter for I
where
    I: IntoIterator,
    (Self, <Self as IntoIterator>::Item): TagIterInner<OuterSelf = Self>,
{
    type Iter = <(Self, <Self as IntoIterator>::Item) as TagIterInner>::Iter;
    fn into_tag_iter(self) -> Self::Iter {
        <(Self, <Self as IntoIterator>::Item) as TagIterInner>::into_iter(self)
    }
}

/// At the time being, rust throws false "overlapping implementation"
/// errors when one tries to implement a trait for types that implement
/// a trait, but with disjoint associated types
///
/// in our concrete case, we would like to implement `IntoIdIter` for
/// `I: IntoIterator<Item = Id>` ,
/// `I: IntoIterator<Item = &Id>` , and
/// `I: IntoIterator<Item = &MemDebug<_>>`
/// which unfortunately triggers a compiler error.
///
/// We can use this trait as a trick to explain to the compiler that
/// actually the implementations do not overlap.
pub trait IdIterInner {
    type Iter: Iterator<Item = Id>;
    type OuterSelf;
    fn into_iter(out_self: Self::OuterSelf) -> Self::Iter;
}

/// At the time being, rust throws false "overlapping implementation"
/// errors when one tries to implement a trait for types that implement
/// a trait, but with disjoint associated types
///
/// in our concrete case, we would like to implement `IntoTagIter` for
/// `I: IntoIterator<Item = Tag>` , and
/// `I: IntoIterator<Item = &Tag>`
/// which unfortunately triggers a compiler error.
///
/// We can use this trait as a trick to explain to the compiler that
/// actually the implementations do not overlap.
pub trait TagIterInner {
    type Iter: Iterator<Item = Tag>;
    type OuterSelf;
    fn into_iter(out_self: Self::OuterSelf) -> Self::Iter;
}

impl<I: IntoIterator<Item = Id>> IdIterInner for (I, Id) {
    type OuterSelf = I;
    type Iter = <I as IntoIterator>::IntoIter;
    #[inline]
    fn into_iter(out_self: Self::OuterSelf) -> Self::Iter {
        out_self.into_iter()
    }
}

impl<'a, I: IntoIterator<Item = &'a Id>> IdIterInner for (I, &'a Id) {
    type Iter = DerefMap<'a, Id, <I as IntoIterator>::IntoIter>;
    type OuterSelf = I;
    fn into_iter(out_self: Self::OuterSelf) -> Self::Iter {
        DerefMap {
            iter: out_self.into_iter(),
        }
    }
}

impl<'a, Data: 'a, I: IntoIterator<Item = &'a super::MemDebug<Data>>> IdIterInner
    for (I, &'a super::MemDebug<Data>)
{
    type Iter = MemDebugIdDerefMap<'a, Data, <I as IntoIterator>::IntoIter>;
    type OuterSelf = I;
    fn into_iter(out_self: Self::OuterSelf) -> Self::Iter {
        MemDebugIdDerefMap {
            iter: out_self.into_iter(),
        }
    }
}

impl<I: IntoIterator<Item = Tag>> TagIterInner for (I, Tag) {
    type OuterSelf = I;
    type Iter = <I as IntoIterator>::IntoIter;
    #[inline]
    fn into_iter(out_self: Self::OuterSelf) -> Self::Iter {
        out_self.into_iter()
    }
}

impl<'a, I: IntoIterator<Item = &'a Tag>> TagIterInner for (I, &'a Tag) {
    type Iter = DerefMap<'a, Tag, <I as IntoIterator>::IntoIter>;
    type OuterSelf = I;
    fn into_iter(out_self: Self::OuterSelf) -> Self::Iter {
        DerefMap {
            iter: out_self.into_iter(),
        }
    }
}

/// Iterator adapter that replaces `iter.map(|r| *r)`
/// This structure only exists because `Map<Iterator, Function>` is
/// not nameable if `Function` is a specific function, and not a
/// generic type that implements `FnOnce`
pub struct DerefMap<'a, Item: 'a, I: Iterator<Item = &'a Item>> {
    iter: I,
}

impl<'a, Item: Copy, I: Iterator<Item = &'a Item>> Iterator for DerefMap<'a, Item, I> {
    type Item = Item;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|ref_item| *ref_item)
    }
}

/// Iterator adapter that replaces `iter.map(|r| r.id())`
/// This structure only exists because `Map<Iterator, Function>` is
/// not nameable if `Function` is a specific function, and not a
/// generic type that implements `FnOnce`
pub struct MemDebugIdDerefMap<'a, Data: 'a, I: Iterator<Item = &'a super::MemDebug<Data>>> {
    iter: I,
}

impl<'a, Data: 'a, I: Iterator<Item = &'a super::MemDebug<Data>>> Iterator
    for MemDebugIdDerefMap<'a, Data, I>
{
    type Item = Id;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|ref_fd| ref_fd.id())
    }
}
