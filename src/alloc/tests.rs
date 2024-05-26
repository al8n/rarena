use core::marker::PhantomData;

use super::*;

fn alloc_aligned_non_zero_size() {
  let arena = Arena::<u32>::new(100); // Create an arena with capacity 100
  let result = arena.alloc::<u32>().unwrap();
  assert_eq!(*result, 0);

  let result = arena.alloc::<u64>().unwrap();
  assert_eq!(*result, 0);
}

#[test]
fn test_alloc_aligned_non_zero_size() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_aligned_non_zero_size();
  });

  #[cfg(not(feature = "loom"))]
  alloc_aligned_non_zero_size();
}

fn alloc_unaligned_non_zero_size() {
  let arena = Arena::<u32>::new(100); // Create an arena with capacity 100
  let result = arena.alloc_unaligned::<u64>().unwrap();
  assert_eq!(*result, 0);

  let result = arena.alloc_unaligned::<u8>().unwrap();
  assert_eq!(*result, 0);
}

#[test]
#[cfg_attr(miri, ignore)]
fn test_alloc_unaligned_non_zero_size() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_unaligned_non_zero_size();
  });

  #[cfg(not(feature = "loom"))]
  alloc_unaligned_non_zero_size();
}

#[allow(clippy::unit_cmp)]
fn alloc_aligned_zero_size() {
  let arena = Arena::<u32>::new(100); // Create an arena with capacity 100
  for i in 0..1000 {
    let result = arena.alloc::<()>().unwrap();
    assert_eq!(*result, (), "{i}");

    let result = arena.alloc::<PhantomData<Vec<u8>>>().unwrap();
    assert_eq!(*result, PhantomData, "{i}");
  }
}

#[test]
fn test_alloc_aligned_zero_size() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_aligned_zero_size();
  });

  #[cfg(not(feature = "loom"))]
  alloc_aligned_zero_size();
}

#[allow(clippy::unit_cmp)]
fn alloc_unaligned_zero_size() {
  let arena = Arena::<u32>::new(100);
  for i in 0..1000 {
    let result = arena.alloc_unaligned::<()>().unwrap();
    assert_eq!(*result, (), "{i}");

    let result = arena.alloc_unaligned::<PhantomData<Vec<u8>>>().unwrap();
    assert_eq!(*result, PhantomData, "{i}");
  }
}

#[test]
fn test_alloc_unaligned_zero_size() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_unaligned_zero_size();
  });

  #[cfg(not(feature = "loom"))]
  alloc_unaligned_zero_size();
}

#[cfg(feature = "std")]
fn concurrent_alloc() {
  #[cfg(feature = "loom")]
  use loom::thread;
  #[cfg(not(feature = "loom"))]
  use std::thread;

  #[cfg(not(feature = "loom"))]
  const THREADS: usize = 4;
  #[cfg(feature = "loom")]
  const THREADS: usize = 2;

  #[cfg(not(feature = "loom"))]
  const ITERATIONS: usize = 100;
  #[cfg(feature = "loom")]
  const ITERATIONS: usize = 2;

  // Create an arena with a capacity large enough for concurrent allocations
  let arena = Arena::<u32>::new(1024 * 1024);

  let handles: Vec<_> = (0..THREADS)
    .map(|_| {
      let arena = arena.clone();

      thread::spawn(move || {
        // Each thread attempts multiple allocations
        for _ in 0..ITERATIONS {
          let mut result = arena.alloc::<u64>().unwrap();
          assert_eq!(*result, 0);
          *result = 10;
          assert_eq!(*result, 10);
        }
      })
    })
    .collect();

  // Wait for all threads to finish
  for handle in handles {
    handle.join().unwrap();
  }
}

#[test]
#[cfg(feature = "std")]
fn test_concurrent_alloc() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    concurrent_alloc();
  });

  #[cfg(not(feature = "loom"))]
  concurrent_alloc();
}
