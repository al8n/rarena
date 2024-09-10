#[cfg(not(feature = "loom"))]
use super::*;

#[cfg(not(feature = "loom"))]
const OPTIONS: ArenaOptions = ArenaOptions::new();

#[test]
#[cfg(not(feature = "loom"))]
fn allocate_slow_path_optimistic_vec() {
  run(|| {
    allocate_slow_path(Arena::new(OPTIONS).unwrap());
  });
}

#[test]
#[cfg(not(feature = "loom"))]
fn allocate_slow_path_optimistic_vec_unify() {
  run(|| {
    allocate_slow_path(Arena::new(OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_allocate_slow_path_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    allocate_slow_path(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segments_vec() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(Arena::new(OPTIONS).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segments_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(Arena::new(OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segments_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_allocate_slow_path_optimistic_concurrent_create_segments_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    allocate_slow_path_concurrent_create_segments(
      Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segments_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path_concurrent_create_segments(
      Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segments_mmap_anon_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(Arena::new(OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_vec() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(Arena::new(OPTIONS).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    allocate_slow_path_concurrent_acquire_from_segment(
      Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path_concurrent_acquire_from_segment(
      Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_acquire_from_segment_mmap_anon_unify() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_vec() {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::new(ArenaOptions::new()).unwrap(),
    );
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(
      "test_allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap",
    );
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_optimistic_concurrent_create_segment_and_acquire_from_segment_mmap_anon_unify(
) {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}
