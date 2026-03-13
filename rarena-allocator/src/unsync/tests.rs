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
  let _ = arena.truncate(2048);

  assert_eq!(arena.allocated(), allocated);
  assert_eq!(arena.capacity(), 2048);

  unsafe {
    assert_eq!(arena.get_bytes(offset, 100), [1u8; 100]);
  }

  let _ = arena.truncate(0);
  assert_eq!(arena.allocated(), allocated);
  assert_eq!(arena.capacity(), allocated);

  unsafe {
    assert_eq!(arena.get_bytes(offset, 100), [1u8; 100]);
  }

  let err = arena.alloc_bytes(10).unwrap_err();
  assert!(matches!(err, Error::InsufficientSpace { .. }));

  let _ = arena.truncate(allocated + 100);
  assert_eq!(arena.allocated(), allocated);
  assert_eq!(arena.capacity(), allocated + 100);

  let b = arena.alloc_bytes(10).unwrap();
  assert_eq!(b.capacity(), 10);
}

#[test]
fn test_truncate_vec() {
  crate::tests::run(|| {
    let arena = Options::new().with_capacity(1024).alloc::<Arena>().unwrap();
    truncate(arena);
  });
}

#[test]
fn test_truncate_vec_unify() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(1024)
      .with_unify(true)
      .alloc::<Arena>()
      .unwrap();
    truncate(arena);
  })
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn test_truncate_map_anon() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(1024)
      .map_anon::<Arena>()
      .unwrap();
    truncate(arena);
  })
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn test_truncate_map_anon_unify() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(1024)
      .with_unify(true)
      .map_anon::<Arena>()
      .unwrap();
    truncate(arena);
  })
}

#[test]
#[cfg(not(feature = "loom"))]
fn test_alloc_type_in_slow_path() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(2048)
      .with_freelist(crate::Freelist::Optimistic)
      .alloc::<Arena>()
      .unwrap();

    // Create segments (non-detached allocs become segments when main is full)
    for i in 1..=5 {
      let _ = arena.alloc_bytes(i * 100).unwrap();
    }
    let remaining = arena.remaining();
    let _ = arena.alloc_bytes(remaining as u32).unwrap();

    // Now allocate typed objects from segments (slow path)
    for _ in 0..3 {
      let _ = unsafe { arena.alloc::<u32>() };
    }
  });
}

#[test]
#[cfg(not(feature = "loom"))]
fn test_alloc_type_in_slow_path_pessimistic() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(2048)
      .with_freelist(crate::Freelist::Pessimistic)
      .alloc::<Arena>()
      .unwrap();

    for i in 1..=5 {
      let _ = arena.alloc_bytes(i * 100).unwrap();
    }
    let remaining = arena.remaining();
    let _ = arena.alloc_bytes(remaining as u32).unwrap();

    for _ in 0..3 {
      let _ = unsafe { arena.alloc::<u32>() };
    }
  });
}

#[test]
#[cfg(not(feature = "loom"))]
fn test_alloc_aligned_in_slow_path() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(2048)
      .with_freelist(crate::Freelist::Optimistic)
      .alloc::<Arena>()
      .unwrap();

    for i in 1..=5 {
      let _ = arena.alloc_bytes(i * 100).unwrap();
    }
    let remaining = arena.remaining();
    let _ = arena.alloc_bytes(remaining as u32).unwrap();

    for _ in 0..3 {
      let _ = arena.alloc_aligned_bytes::<u64>(8);
    }
  });
}

#[test]
#[cfg(not(feature = "loom"))]
fn test_alloc_aligned_in_slow_path_pessimistic() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(2048)
      .with_freelist(crate::Freelist::Pessimistic)
      .alloc::<Arena>()
      .unwrap();

    for i in 1..=5 {
      let _ = arena.alloc_bytes(i * 100).unwrap();
    }
    let remaining = arena.remaining();
    let _ = arena.alloc_bytes(remaining as u32).unwrap();

    for _ in 0..3 {
      let _ = arena.alloc_aligned_bytes::<u64>(8);
    }
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[cfg_attr(miri, ignore)]
fn test_truncate_map() {
  crate::tests::run(|| {
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
  })
}

#[test]
#[cfg(feature = "std")]
fn test_print_segment_list_optimistic() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(4096)
      .with_freelist(crate::Freelist::Optimistic)
      .alloc::<Arena>()
      .unwrap();

    // Create segments by allocating, detaching, then deallocating
    let mut blocks = Vec::new();
    for i in 1..=3 {
      let mut b = arena.alloc_bytes(i * 100).unwrap();
      unsafe { b.detach() };
      blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
    }

    // Fill remaining
    let remaining = arena.remaining();
    if remaining > 0 {
      let mut b = arena.alloc_bytes(remaining as u32).unwrap();
      unsafe { b.detach() };
    }

    // Dealloc to create freelist entries
    for (offset, size) in blocks {
      unsafe { arena.dealloc(offset, size) };
    }

    // print_segment_list traverses the freelist and prints nodes
    arena.print_segment_list();
  });
}

#[test]
#[cfg(feature = "std")]
fn test_print_segment_list_pessimistic() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(4096)
      .with_freelist(crate::Freelist::Pessimistic)
      .alloc::<Arena>()
      .unwrap();

    let mut blocks = Vec::new();
    for i in 1..=3 {
      let mut b = arena.alloc_bytes(i * 100).unwrap();
      unsafe { b.detach() };
      blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
    }

    let remaining = arena.remaining();
    if remaining > 0 {
      let mut b = arena.alloc_bytes(remaining as u32).unwrap();
      unsafe { b.detach() };
    }

    for (offset, size) in blocks {
      unsafe { arena.dealloc(offset, size) };
    }

    arena.print_segment_list();
  });
}

#[test]
#[cfg(feature = "std")]
fn test_print_segment_list_empty() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(4096)
      .with_freelist(crate::Freelist::Optimistic)
      .alloc::<Arena>()
      .unwrap();

    // Print empty freelist - exercises the sentinel-only path
    arena.print_segment_list();
  });
}

/// Test SegmentNode Debug impl for unsync Arena
#[test]
fn test_unsync_segment_node_debug() {
  let node = SegmentNode(UnsafeCell::new(encode_segment_node(100, 200)));
  let debug_str = format!("{:?}", node);
  assert!(debug_str.contains("SegmentNode"));
  assert!(debug_str.contains("offset"));
  assert!(debug_str.contains("next"));
}
