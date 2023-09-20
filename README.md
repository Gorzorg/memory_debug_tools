# Content

This crate contains tools that can help test and debug memory errors in Rust programs that either contain, or depend on, untrustworthy unsafe code.

The tools provided here are motivated by the fact that it is not super easy to write unit tests for algorithms that can cause undefined behavior.

The main structure defined by the crate is `MemDebug`.  
It is a wrapper data structure intended exclusively for test environment, that is capable of detecting when undefined behavior is about to be applied by using it.

For example

```rust
{
    // The first argument is the data being
    // wrapped, the second is not relevant now.
    let a = MemDebug::new(Box::new(u8), []);

    // We are treating `a` as if it was `Copy`,
    // even if it is not. In this case,
    // we are copying a `Box` value,
    // which easily leads to undefined behavior.
    let b = unsafe{
        std::ptr::read(&a as *const _)
    };
    // At the end of this scope both `a` and
    // `b` are dropped, but the drop method 
    // of `MemDebug` notices it, prevents
    // the double drop of the `Box`,
    // and raises a panic.
}
```

## How is it achieved?

When a `MemDebug` instance is created, the information is stored in a global register that tracks all instances.

The struct is defined as
```rust
struct MemDebug<Data> {
    data: std::mem::ManuallyDrop<Data>,
    id: Id,
}
```

Where every new instance of the struct is assigned its new unique id. The id is used to keep track of the instance.

When a `MemDebug` is dropped, its entry is removed from the register. If a drop attempt occurs when no corresponding entry is in the register, a panic is raised, and the drop of the wrapped data is prevented.

Similarly, when dereferencing the wrapped data, a check on the global register is made, and if no corresponding entry is found, a panic is raised.

## Why only test environment?

Every operation that interacts with the global register requires acquiring at least one mutex guard, to allow for the testing of multi-threaded algorithms. 

This can drastically affect performance, and for this reason, I discourage the use of this crate in non-test code.

## What are `Tag`s for?

`Tag`s are a way to track the path that `MemDebug` instances take in memory.

They are additional information that is attached to every entry in the global register that tracks `MemDebug` values.

The simplest use case for tags is detecting memory leaks: one can wrap in `MemDebug` all the values that are suspected of being subject to leaks, and then a tag can be applied to those values.

At the end of the algorithm, one can test if any `MemDebug` instances that are still alive are tagged. If yes, a memory leak is occurring.

```rust
let tag = Tag::from(1);
// We create a boxed `MemDebug` value,
// we tag it with `tag`,
// and then we leak the box.
let a = Box::new(MemDebug::new(42, [tag]));
// Every `MemDebug` instance has a unique `id`.
let id = a.id(); 
Box::leak(a);

// Here, we can detect that the value
// leaked by `a` is still alive.
// For reference, `s` is the set
// of all `id` values of `MemDebug`
// instances tagged with `tag`.
assert!(
    MemDebug::assert_on_tag(
        tag,
        |s| s.contains(&id)
    )
);
```

Use cases for tags go beyond that, and the whole tag concept is conceived as a general purpose instrument.

For example, one can add tags to instances of `MemDebug` that get processed by some specific functions, so that one can at least partly trace how the single values were treated by the algorithm.

```rust
let mut a: Vec<_> = (0..10).map(|i| MemDebug::new(i, [])).collect();
let a_id: Vec<_> = a.iter().map(|x| x.id()).collect();

let tag = Tag::from(1);

fn compute(x: &mut MemDebug<i32>, tag: Tag) {
    if *x % 2 == 0 {
        /* some heavy computation */
        MemDebug::add_tags(x.id(), [tag]).unwrap();
    } else {
        /* some light computation */
    }
}

// We apply `compute` to every element in `a`.
a.iter_mut().for_each(|r| compute(r, tag));

// We fetch all the ids of instances that have
// been tagged by `compute`.
let tagged_ids = MemDebug::get_tags()
        .get(&tag)
        .map(|s| s.clone())
        .unwrap_or_default();

// Now we know which items required a lot
// of computation to be processed.
assert_eq!(
    tagged_ids,
    BTreeSet::from_iter(a_id[0], a_id[2], a_id[4], a_id[6], a_id[8])
);
```

## A note on `Clone`

An implementation of

```rust
impl<Data: Clone> Clone for MemDebug<Data> {...}
```

is provided. Attention should be paid to the fact that the clone of a `MemDebug` instance has a new unique `id`, but all the tags to the original value are copied to the clone.

Keep this in mind when writing tests.