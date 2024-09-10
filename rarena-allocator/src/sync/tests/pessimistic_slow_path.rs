#[cfg(not(feature = "loom"))]
use super::*;

#[cfg(not(feature = "loom"))]
const OPTIONS: ArenaOptions = ArenaOptions::new().with_freelist(Freelist::Pessimistic);

#[cfg(not(feature = "loom"))]
fn allocate_slow_path_pessimistic(l: Arena) {
  // make some segments
  for i in 1..=5 {
    let _ = l.alloc_bytes(i * 50).unwrap();
  }

  let remaining = l.remaining();
  let _ = l.alloc_bytes(remaining as u32).unwrap();

  // 751 -> 501 -> 301 -> 151 -> 51 -> 1

  // allocate from segments
  for i in (1..=5).rev() {
    l.alloc_bytes(i * 50 - MAX_SEGMENT_NODE_SIZE).unwrap();
  }
}

#[test]
#[cfg(not(feature = "loom"))]
fn allocate_slow_path_pessimistic_vec() {
  run(|| {
    allocate_slow_path_pessimistic(Arena::new(OPTIONS).unwrap());
  });
}

#[test]
#[cfg(not(feature = "loom"))]
fn allocate_slow_path_pessimistic_vec_unify() {
  run(|| {
    allocate_slow_path_pessimistic(Arena::new(OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_allocate_slow_path_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    allocate_slow_path_pessimistic(
      Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path_pessimistic(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_pessimistic_concurrent_create_segments_vec() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(Arena::new(OPTIONS).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_pessimistic_concurrent_create_segments_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(Arena::new(OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_concurrent_create_segments_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_allocate_slow_path_pessimistic_concurrent_create_segments_mmap");
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
fn allocate_slow_path_pessimistic_concurrent_create_segments_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path_concurrent_create_segments(
      Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_concurrent_create_segments_mmap_anon_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segments(Arena::new(OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_pessimistic_concurrent_acquire_from_segment_vec() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(Arena::new(OPTIONS).unwrap());
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_pessimistic_concurrent_acquire_from_segment_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_concurrent_acquire_from_segment_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join("test_allocate_slow_path_pessimistic_concurrent_acquire_from_segment_mmap");
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
fn allocate_slow_path_pessimistic_concurrent_acquire_from_segment_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path_concurrent_acquire_from_segment(
      Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_concurrent_acquire_from_segment_mmap_anon_unify() {
  run(|| {
    allocate_slow_path_concurrent_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_pessimistic_concurrent_create_segment_and_acquire_from_segment_vec() {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::new(ArenaOptions::new()).unwrap(),
    );
  });
}

#[test]
#[cfg(all(not(feature = "loom"), feature = "std"))]
fn allocate_slow_path_pessimistic_concurrent_create_segment_and_acquire_from_segment_vec_unify() {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_concurrent_create_segment_and_acquire_from_segment_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(
      "test_allocate_slow_path_pessimistic_concurrent_create_segment_and_acquire_from_segment_mmap",
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
fn allocate_slow_path_pessimistic_concurrent_create_segment_and_acquire_from_segment_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn allocate_slow_path_pessimistic_concurrent_create_segment_and_acquire_from_segment_mmap_anon_unify(
) {
  run(|| {
    allocate_slow_path_concurrent_create_segment_and_acquire_from_segment(
      Arena::new(OPTIONS.with_unify(true)).unwrap(),
    );
  });
}
