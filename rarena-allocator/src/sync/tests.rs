#![allow(dead_code)]

use super::*;

mod optimistic_slow_path;
mod pessimistic_slow_path;

common_unit_tests!("sync": Arena {
  type Header = crate::sync::sealed::Header;
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

#[test]
#[cfg(not(feature = "loom"))]
fn test_alloc_type_in_slow_path_optimistic() {
  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(2048)
      .with_freelist(crate::Freelist::Optimistic)
      .alloc::<Arena>()
      .unwrap();

    // Create segments large enough to hold typed allocations after node overhead
    for i in 1..=5 {
      let _ = arena.alloc_bytes(i * 100).unwrap();
    }
    let remaining = arena.remaining();
    let _ = arena.alloc_bytes(remaining as u32).unwrap();

    // Now allocate typed objects (goes through alloc_in slow path)
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
fn test_alloc_aligned_in_slow_path_optimistic() {
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

#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_concurrent_create_segments(l: Arena) {
  use std::sync::{Arc, Barrier};

  let b = Arc::new(Barrier::new(5));
  let allocated = Arc::new(crossbeam_queue::ArrayQueue::new(5));
  let mut handles = std::vec::Vec::new();

  // make some segments
  for i in 1..=5 {
    let l = l.clone();
    let b = b.clone();
    let allocated = allocated.clone();
    handles.push(std::thread::spawn(move || {
      b.wait();
      let bytes = l.alloc_bytes_owned(i * 50).unwrap();
      let _ = allocated.push(bytes);
    }));
  }

  for handle in handles {
    handle.join().unwrap();
  }

  let remaining = l.remaining();
  let mut remaining = l.alloc_bytes(remaining as u32).unwrap();
  unsafe {
    remaining.detach();
  }
  drop(allocated);

  // allocate from segments
  for i in (1..=5).rev() {
    let mut b = l.alloc_bytes(i * 50 - MAX_SEGMENT_NODE_SIZE).unwrap();
    unsafe {
      b.detach();
    }
  }

  while l.refs() > 1 {
    std::thread::yield_now();
  }
}

#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_concurrent_acquire_from_segment(l: Arena) {
  use std::sync::{Arc, Barrier};

  let b = Arc::new(Barrier::new(5));
  let mut allocated = std::vec::Vec::new();

  // make some segments
  for _ in 1..=5 {
    let bytes = l.alloc_bytes(50).unwrap();
    allocated.push(bytes);
  }

  let remaining = l.remaining();
  let mut remaining = l.alloc_bytes(remaining as u32).unwrap();
  unsafe {
    remaining.detach();
  }
  drop(allocated);

  // allocate from segments
  for _ in (1..=5).rev() {
    let l = l.clone();
    let b = b.clone();
    std::thread::spawn(move || {
      b.wait();
      let mut b = l.alloc_bytes(50 - MAX_SEGMENT_NODE_SIZE).unwrap();
      unsafe {
        b.detach();
      }
      std::thread::yield_now();
    });
  }

  while l.refs() > 1 {
    std::thread::yield_now();
  }
}

#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(l: Arena) {
  use std::sync::{Arc, Barrier};

  let b = Arc::new(Barrier::new(5));
  let allocated = Arc::new(crossbeam_queue::ArrayQueue::new(5));
  let mut handles = std::vec::Vec::new();

  // make some segments
  for _ in 1..=5 {
    let l = l.clone();
    let b = b.clone();
    let allocated = allocated.clone();
    handles.push(std::thread::spawn(move || {
      b.wait();
      let bytes = l.alloc_bytes_owned(50).unwrap();
      let _ = allocated.push(bytes);
    }));
  }

  for handle in handles {
    handle.join().unwrap();
  }

  let remaining = l.remaining();
  let mut remaining = l.alloc_bytes(remaining as u32).unwrap();
  unsafe {
    remaining.detach();
  }
  drop(allocated);

  // allocate from segments
  for _ in (1..=5).rev() {
    let l = l.clone();
    let b = b.clone();
    std::thread::spawn(move || {
      b.wait();
      let mut b = l.alloc_bytes(50 - MAX_SEGMENT_NODE_SIZE).unwrap();
      unsafe {
        b.detach();
      }
    });
  }

  while l.refs() > 1 {
    std::thread::yield_now();
  }
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

    arena.print_segment_list();
  });
}

/// High contention test: many threads doing alloc + dealloc simultaneously
/// to trigger CAS retry paths in optimistic_dealloc, find_position, etc.
#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn test_high_contention_alloc_dealloc_optimistic() {
  use std::sync::{Arc, Barrier};

  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(256 << 10)
      .with_freelist(crate::Freelist::Optimistic)
      .alloc::<Arena>()
      .unwrap();

    let barrier = Arc::new(Barrier::new(8));
    let mut handles = Vec::new();

    for _ in 0..8 {
      let a = arena.clone();
      let b = barrier.clone();
      handles.push(std::thread::spawn(move || {
        b.wait();
        for _ in 0..100 {
          let mut bytes = match a.alloc_bytes(64) {
            Ok(b) => b,
            Err(_) => continue,
          };
          unsafe { bytes.detach() };
          let offset = bytes.buffer_offset() as u32;
          let size = bytes.buffer_capacity() as u32;
          drop(bytes);
          // Immediately dealloc to create freelist contention
          unsafe { a.dealloc(offset, size) };
        }
      }));
    }

    for h in handles {
      h.join().unwrap();
    }
  });
}

/// High contention test with pessimistic freelist
#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn test_high_contention_alloc_dealloc_pessimistic() {
  use std::sync::{Arc, Barrier};

  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(256 << 10)
      .with_freelist(crate::Freelist::Pessimistic)
      .alloc::<Arena>()
      .unwrap();

    let barrier = Arc::new(Barrier::new(8));
    let mut handles = Vec::new();

    for _ in 0..8 {
      let a = arena.clone();
      let b = barrier.clone();
      handles.push(std::thread::spawn(move || {
        b.wait();
        for _ in 0..100 {
          let mut bytes = match a.alloc_bytes(64) {
            Ok(b) => b,
            Err(_) => continue,
          };
          unsafe { bytes.detach() };
          let offset = bytes.buffer_offset() as u32;
          let size = bytes.buffer_capacity() as u32;
          drop(bytes);
          unsafe { a.dealloc(offset, size) };
        }
      }));
    }

    for h in handles {
      h.join().unwrap();
    }
  });
}

/// Concurrent discard_freelist racing with alloc_bytes (optimistic).
/// Previously livelocked due to dangling REMOVED nodes when sentinel CAS failed.
#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn test_concurrent_discard_freelist_optimistic() {
  use std::sync::{Arc, Barrier};

  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(256 << 10)
      .with_freelist(crate::Freelist::Optimistic)
      .alloc::<Arena>()
      .unwrap();

    // Pre-populate freelist with many segments
    let mut offsets = Vec::new();
    for _ in 0..200 {
      let mut bytes = arena.alloc_bytes(128).unwrap();
      unsafe { bytes.detach() };
      offsets.push((bytes.buffer_offset() as u32, bytes.buffer_capacity() as u32));
    }
    let remaining = arena.remaining();
    let mut fill = arena.alloc_bytes(remaining as u32).unwrap();
    unsafe { fill.detach() };
    for (offset, size) in offsets {
      unsafe { arena.dealloc(offset, size) };
    }

    let barrier = Arc::new(Barrier::new(3));
    let mut handles = Vec::new();

    // Thread 1: discard_freelist
    {
      let a = arena.clone();
      let b = barrier.clone();
      handles.push(std::thread::spawn(move || {
        b.wait();
        let _ = a.discard_freelist();
      }));
    }

    // Thread 2 & 3: alloc_bytes from freelist
    for _ in 0..2 {
      let a = arena.clone();
      let b = barrier.clone();
      handles.push(std::thread::spawn(move || {
        b.wait();
        for _ in 0..50 {
          let _ = a.alloc_bytes(64);
        }
      }));
    }

    for h in handles {
      h.join().unwrap();
    }
  });
}

/// Concurrent discard_freelist racing with alloc_bytes (pessimistic).
#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn test_concurrent_discard_freelist_pessimistic() {
  use std::sync::{Arc, Barrier};

  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(256 << 10)
      .with_freelist(crate::Freelist::Pessimistic)
      .alloc::<Arena>()
      .unwrap();

    let mut offsets = Vec::new();
    for _ in 0..200 {
      let mut bytes = arena.alloc_bytes(128).unwrap();
      unsafe { bytes.detach() };
      offsets.push((bytes.buffer_offset() as u32, bytes.buffer_capacity() as u32));
    }
    let remaining = arena.remaining();
    let mut fill = arena.alloc_bytes(remaining as u32).unwrap();
    unsafe { fill.detach() };
    for (offset, size) in offsets {
      unsafe { arena.dealloc(offset, size) };
    }

    let barrier = Arc::new(Barrier::new(3));
    let mut handles = Vec::new();

    {
      let a = arena.clone();
      let b = barrier.clone();
      handles.push(std::thread::spawn(move || {
        b.wait();
        let _ = a.discard_freelist();
      }));
    }

    for _ in 0..2 {
      let a = arena.clone();
      let b = barrier.clone();
      handles.push(std::thread::spawn(move || {
        b.wait();
        for _ in 0..50 {
          let _ = a.alloc_bytes(64);
        }
      }));
    }

    for h in handles {
      h.join().unwrap();
    }
  });
}

/// Concurrent slow path allocations racing with each other (pessimistic).
#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn test_concurrent_slow_path_alloc_pessimistic() {
  use std::sync::{Arc, Barrier};

  crate::tests::run(|| {
    let arena = Options::new()
      .with_capacity(256 << 10)
      .with_freelist(crate::Freelist::Pessimistic)
      .alloc::<Arena>()
      .unwrap();

    let mut offsets = Vec::new();
    for _ in 0..200 {
      let mut bytes = arena.alloc_bytes(128).unwrap();
      unsafe { bytes.detach() };
      offsets.push((bytes.buffer_offset() as u32, bytes.buffer_capacity() as u32));
    }
    let remaining = arena.remaining();
    let mut fill = arena.alloc_bytes(remaining as u32).unwrap();
    unsafe { fill.detach() };
    for (offset, size) in offsets {
      unsafe { arena.dealloc(offset, size) };
    }

    let barrier = Arc::new(Barrier::new(4));
    let mut handles = Vec::new();

    for _ in 0..4 {
      let a = arena.clone();
      let b = barrier.clone();
      handles.push(std::thread::spawn(move || {
        b.wait();
        for _ in 0..50 {
          let _ = a.alloc_bytes(64);
        }
      }));
    }

    for h in handles {
      h.join().unwrap();
    }
  });
}

/// Test SegmentNode Debug impl for sync Arena
#[test]
fn test_sync_segment_node_debug() {
  use core::sync::atomic::AtomicU64;
  let node = SegmentNode {
    size_and_next: AtomicU64::new(encode_segment_node(100, 200)),
  };
  let debug_str = format!("{:?}", node);
  assert!(debug_str.contains("SegmentNode"));
  assert!(debug_str.contains("offset"));
  assert!(debug_str.contains("next"));
}
