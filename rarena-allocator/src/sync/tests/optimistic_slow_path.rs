#[cfg(all(not(feature = "loom"), feature = "std"))]
use super::*;

#[cfg(all(not(feature = "loom"), feature = "std"))]
use crate::tests::run;

#[cfg(all(not(feature = "loom"), feature = "std"))]
const OPTIONS: Options = Options::new()
  .with_capacity(1024)
  .with_freelist(Freelist::Optimistic);

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segments_vec() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(OPTIONS.alloc().unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segments_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(OPTIONS.with_unify(true).alloc().unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segments_mmap() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_allocate_slow_path_optimistic_concurrent_create_segments_mmap");

    let arena = OPTIONS
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut(p)
      .unwrap();
    allocate_slow_path_concurrent_create_segments(arena);
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segments_mmap_anon() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(OPTIONS.map_anon().unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segments_mmap_anon_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(OPTIONS.with_unify(true).map_anon().unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_vec() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(OPTIONS.alloc().unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(OPTIONS.with_unify(true).alloc().unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap");
    let arena = OPTIONS
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut(p)
      .unwrap();
    allocate_slow_path_concurrent_acquire_from_segment(arena);
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap_anon() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(OPTIONS.map_anon().unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap_anon_unify() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(
      OPTIONS.with_unify(true).map_anon().unwrap(),
    );
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_vec() {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(OPTIONS.alloc().unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      OPTIONS.with_unify(true).alloc().unwrap(),
    );
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap() {
  run(|| unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(
      "test_allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap",
    );
    let arena = OPTIONS
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut(p)
      .unwrap();
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(arena);
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap_anon() {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      OPTIONS.map_anon().unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap_anon_unify()
 {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      OPTIONS.with_unify(true).map_anon().unwrap(),
    );
  });
}
