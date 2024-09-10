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
