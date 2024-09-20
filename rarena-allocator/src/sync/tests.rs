#![allow(dead_code)]

#[cfg(all(not(feature = "loom"), feature = "std"))]
use crate::Memory as _;

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
