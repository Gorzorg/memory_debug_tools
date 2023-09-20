use std::{collections::BTreeSet, ops::Deref};

use super::*;

/// Minimal test to prove that when a `MemDebug` item is dropped,
/// the drop is detected in the allocation tracker.
#[test]
fn test_alive() {
    let a: MemDebug = Default::default();
    let id_a = a.id();
    let id_b;
    {
        let b: MemDebug = Default::default();
        id_b = b.id();

        // both `a` and `b` should be alive at this point.
        assert!(MemDebug::is_alive(id_a));
        assert!(MemDebug::is_alive(id_b));
    }
    // now `a` should still be alive, while `b` should have been dropped.
    assert!(MemDebug::is_alive(id_a));
    assert!(!MemDebug::is_alive(id_b));
}

/// This code causes the double drop of a `MemDebug` instance.
/// Any such scenario should cause a panic.
#[test]
#[should_panic]
fn test_direct_double_drop() {
    let a: MemDebug = Default::default();
    let a_id = a.id();
    unsafe {
        // Here we create another instance that has the same memory content
        // as `a`. This means that also the id is the same, so that when
        // this instance is dropped, the id of `a` is tracked as
        // already dropped.
        let _b = core::ptr::read::<MemDebug>(a.as_ptr());

        // now `b` is still alive, so `a` should also be still marked as alive.
        assert!(MemDebug::is_alive(a_id));
    }
    // now `b` has been dropped. Since the id of `b` was the same as the id of
    // `a`, `a` should now be marked as already dropped.
    assert!(!MemDebug::is_alive(a_id));

    // now `a` goes out of scope, and causes a panic.
}

/// This code causes the double drop of a `MemDebug` instance.
/// Any such scenario should cause a panic.
#[test]
#[should_panic]
fn test_side_effect_double_drop() {
    let a: MemDebug = Default::default();
    let b = MemDebug::new(a, []);
    let _c = MemDebug::new(unsafe { core::ptr::read(b.deref() as *const _) }, []);
}

/// This proves that the drop of an uninitialized variable can be detected.
#[test]
#[should_panic]
fn test_uninit_drop() {
    let mut a = core::mem::MaybeUninit::<MemDebug>::uninit();
    unsafe { a.assume_init_drop() }
}

/// This code proves the fact that memory leaks can be detected.
#[test]
fn test_memory_leak() {
    let tag = MemDebug::create_tag();
    let id;
    {
        // We create a box and then leak it.
        // Before leaking it, we tag the `MemDebug` inside it.
        let a = Box::new(MemDebug::<()>::default());
        assert!(MemDebug::add_tags(a.id(), [tag]).is_ok());
        id = a.id();
        Box::leak(a);
    }
    // Now we make sure that the value inside the box
    // has not been dropped.
    //
    // We can detect this with both the tag, and the id.
    assert!(MemDebug::get_tag(tag).contains(&id));
    assert!(MemDebug::assert_on_alloc(|m| m.contains_key(&id)));
}

/// This test proves that use after free bugs are detected as expected.
#[test]
#[should_panic = "Attempted using a `MemDebug` instance that corresponds to uninitialized, or already dropped, memory."]
fn test_use_after_free() {
    let a = MemDebug::new("something that must not be used after drop", []);
    {
        // b goes out of scope and causes `a` to become invalid.
        let _b = unsafe { core::ptr::read(&a as *const _) };
        //assert!(MemDebug::is_alive(a.id));
    }
    // We are sure that the panic is not caused by `a` going out of scope because
    // we move it in a `ManuallyDrop` instance.
    let c = core::mem::ManuallyDrop::new(a);

    //assert!(!MemDebug::is_alive(a.id));
    // Now the content of `a` has been dropped, and must not be used. We now
    // trigger a panic by trying to dereference `a`.
    let _d = c.deref().deref();
}

#[test]
fn test_tag_tracking() {
    // We create some tags
    let tags: Vec<_> = (0..10).map(|_| MemDebug::create_tag()).collect();
    // We create some `MemDebug` instances, giving them variable amounts of tags
    let mut a: Vec<_> = (0..10)
        .map(|i| MemDebug::<u8>::new(i, tags[0..usize::from(i)].iter().map(|x| *x)))
        .collect();
    let id_vec: Vec<_> = a.iter().map(|fd| fd.id()).collect();
    // We kill half the instances
    a.retain(|fd| (**fd) % 2 == 0);

    // We assert that every tag has the right tagged instances
    for i in 0..10 {
        assert_eq!(MemDebug::is_alive(id_vec[i]), i % 2 == 0);
        let rhs = BTreeSet::from_iter(((i + 1)..10).filter_map(|j| {
            if j % 2 == 0 {
                Some(id_vec[j])
            } else {
                None
            }
        }));
        assert!(*MemDebug::get_tag(tags[i]) == rhs);
    }
    //We assert that the currently alive instances contain the ones we expect.
    let rhs: BTreeSet<_> = a.iter().map(|fd| fd.id()).collect();
    assert!(MemDebug::assert_on_alloc(|map| BTreeSet::from_iter(
        map.iter().map(|(k, _)| *k)
    )
    .is_superset(&rhs)));
}

#[test]
fn test_tag_tracking_2() {
    let tag1 = MemDebug::create_tag();
    let tag2 = MemDebug::create_tag();
    let tag3 = MemDebug::create_tag();

    let a: Vec<_> = (0..4).map(|_| MemDebug::new((), [tag1])).collect();
    let b: Vec<_> = (0..4).map(|_| MemDebug::new((), [tag2])).collect();

    let mut id_vec = vec![];
    id_vec.extend(a.iter().map(|r| r.id()));
    id_vec.extend(b.iter().map(|r| r.id()));

    let mut c: Vec<_> = a
        .into_iter()
        .zip(b.into_iter())
        .map(|(x1, x2)| [x1, x2])
        .flatten()
        .collect();
    assert!(MemDebug::add_tag_to_group(c.iter(), tag3).is_ok());
    let d: Vec<_> = c.drain(4..).collect();

    MemDebug::remove_tag_from_group(c.iter(), tag1);
    MemDebug::remove_tag_from_group(d.iter(), tag2);

    let rhs = BTreeSet::from_iter([id_vec[2], id_vec[3]]);
    assert!(*MemDebug::get_tag(tag1) == rhs);

    let rhs = BTreeSet::from_iter([id_vec[4], id_vec[5]]);
    assert!(*MemDebug::get_tag(tag2) == rhs);

    c.clear();
    let rhs = BTreeSet::from_iter([id_vec[2], id_vec[6], id_vec[3], id_vec[7]]);
    assert!(*MemDebug::get_tag(tag3) == rhs);
    assert!(MemDebug::get_tag(tag2).is_empty());

    let tag4 = MemDebug::create_tag();

    assert!(MemDebug::add_tags(id_vec[7], [tag4]).is_ok());
    assert!(MemDebug::add_tags(id_vec[0], [tag4]).is_err());
    assert_eq!(
        MemDebug::add_tag_to_group(id_vec.iter(), tag4),
        Err(BTreeSet::from_iter([
            id_vec[0], id_vec[4], id_vec[1], id_vec[5]
        ]))
    );
}

#[test]
fn test_clone() {
    let a = MemDebug::new(42, MemDebug::create_tags(3));
    let b = a.clone();
    assert_eq!(*a, *b);
    let tags_by_id = MemDebug::get_tags_by_id();
    assert_eq!(
        *tags_by_id.get(&a.id()).unwrap().lock().unwrap(),
        *tags_by_id.get(&b.id()).unwrap().lock().unwrap()
    );
}

/// Tests the functionality that allows to get multiple mutex guards from the global
/// tag maps.
/// A mutex guard requires `&mut` access to the value that owns the mutex, because if
/// the owner moves somehow the mutex (think of `Vec::<Mutex::<T>>::push`), then
/// the mutex guard will not be able to drop correctly.
/// We provide a functionality that circumvents that problem, by using
/// `Box<Mutex<T>>` instead of `Mutex<T>`
///
/// for a practical demo, see
/// [here](https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=3c62db3a4650cd2f2d6a48f04365fe64)
#[test]
fn test_concurrent_get_tag() {
    let tag1 = MemDebug::create_tag();
    let tag2 = MemDebug::create_tag();
    let md1 = MemDebug::new((), [tag1]);
    let md2 = MemDebug::new((), [tag2]);

    let _md_vec: Vec<MemDebug>;
    {
        // Concurrent read only mutex guards to values of the same maps.
        let r1 = MemDebug::get_tag(tag1);
        let r2 = MemDebug::get_tag(tag2);
        let s1 = MemDebug::get_tags_on_id(md1.id());
        let s2 = MemDebug::get_tags_on_id(md2.id());

        // We assert that the read-only functionality works as expected
        assert!(
            r1.contains(&md1.id())
                && r1.len() == 1
                && r2.contains(&md2.id())
                && r2.len() == 1
                && s1.contains(&tag1)
                && s1.len() == 1
                && s2.contains(&tag2)
                && s2.len() == 1
        );

        // We cause the global tag maps to re-allocate their entries.
        _md_vec = (0..10000)
            .map(|_| MemDebug::new((), [MemDebug::create_tag()]))
            .collect()

        // Now `r1`, `r2`, `s1`, `s2` drop. If the mutexes they refer to were moved
        // while the global tag maps were being accessed mutably, their drop
        // leaves the mutexes in an invalid state.
    }

    // We try accessing agein the same values we accessed before
    let r1 = MemDebug::get_tag(tag1);
    let r2 = MemDebug::get_tag(tag2);
    let s1 = MemDebug::get_tags_on_id(md1.id());
    let s2 = MemDebug::get_tags_on_id(md2.id());

    // We check that everything stayed the same in the referred values
    assert!(
        r1.contains(&md1.id())
            && r1.len() == 1
            && r2.contains(&md2.id())
            && r2.len() == 1
            && s1.contains(&tag1)
            && s1.len() == 1
            && s2.contains(&tag2)
            && s2.len() == 1
    );
}
