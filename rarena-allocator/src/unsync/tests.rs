#![allow(dead_code)]

use super::*;

common_unit_tests!("unsync": Arena {
  type Header = crate::unsync::sealed::Header;
  type SegmentNode = super::SegmentNode;
});

#[test]
fn test_meta_eq() {
  let a_ptr = 1u8;
  let b_ptr = 1u8;
  let a = Meta::new(&a_ptr as _, 2, 3);
  let b = Meta::new(&b_ptr as _, 2, 3);
  assert_ne!(a, b);
}

fn truncate(mut arena: Arena) {
  let mut b = arena.alloc_bytes(100).unwrap();
  b.set_len(100);
  b.fill(1);
  unsafe {
    b.detach();
  }
  let offset = b.offset();
  drop(b);

  let allocated = arena.allocated();
  arena.truncate(2048).unwrap();

  assert_eq!(arena.allocated(), allocated);
  assert_eq!(arena.capacity(), 2048);

  unsafe {
    assert_eq!(arena.get_bytes(offset, 100), [1u8; 100]);
  }

  arena.truncate(0).unwrap();
  assert_eq!(arena.allocated(), allocated);
  assert_eq!(arena.capacity(), allocated);

  unsafe {
    assert_eq!(arena.get_bytes(offset, 100), [1u8; 100]);
  }
}

#[test]
fn test_truncate_vec() {
  let arena = Options::new().with_capacity(1024).alloc::<Arena>().unwrap();
  truncate(arena);
}

#[test]
fn test_truncate_vec_unify() {
  let arena = Options::new()
    .with_capacity(1024)
    .with_unify(true)
    .alloc::<Arena>()
    .unwrap();
  truncate(arena);
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn test_truncate_map_anon() {
  let arena = Options::new()
    .with_capacity(1024)
    .map_anon::<Arena>()
    .unwrap();
  truncate(arena);
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn test_truncate_map_anon_unify() {
  let arena = Options::new()
    .with_capacity(1024)
    .with_unify(true)
    .map_anon::<Arena>()
    .unwrap();
  truncate(arena);
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(miri, ignore)]
fn test_truncate_map() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_unsync_truncate_map");
  let arena = unsafe {
    Options::new()
      .with_capacity(1024)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<Arena, _>(&p)
      .unwrap()
  };
  truncate(arena);
}
