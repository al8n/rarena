use super::*;

const ARENA_SIZE: usize = 1024;

fn alloc_bytes(a: Arena) {
  let b = a.alloc_bytes(10).unwrap();
  assert_eq!(b.capacity(), 10);
}

#[test]
fn alloc_bytes_vec() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_bytes(Arena::new(ArenaOptions::new()));
  });

  #[cfg(not(feature = "loom"))]
  alloc_bytes(Arena::new(ARENA_SIZE as u32, 8));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_bytes_mmap() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_alloc_bytes_mmap");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  alloc_bytes(Arena::map_mut(p, open_options, mmap_options, 8).unwrap());
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_bytes_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE as usize);
  alloc_bytes(Arena::map_anon(mmap_options, 8).unwrap());
}
