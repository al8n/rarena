#![allow(dead_code)]

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
  alloc_bytes(Arena::new(ArenaOptions::new()));
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
  alloc_bytes(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_bytes_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE as usize);
  alloc_bytes(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
}

fn alloc_heap(a: Arena) {
  let mut b = unsafe { a.alloc::<Vec<u8>>().unwrap() };
  b.write(Vec::with_capacity(10));

  unsafe {
    b.as_mut()
      .extend_from_slice(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

    assert_eq!(b.as_ref().len(), 10);

    b.as_mut().push(128);
    assert_eq!(b.as_ref().len(), 11);
  }
}

#[test]
fn alloc_heap_vec() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_heap(Arena::new(ArenaOptions::new()));
  });

  #[cfg(not(feature = "loom"))]
  alloc_heap(Arena::new(ArenaOptions::new()));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_heap_mmap() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_alloc_heap_mmap");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  alloc_heap(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_heap_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE as usize);
  alloc_heap(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
}

fn alloc_inlined(a: Arena) {
  let mut b = unsafe { a.alloc::<u32>().unwrap() };
  b.write(10);

  unsafe {
    assert_eq!(*b.as_ref(), 10);
    *b.as_mut() = 20;
    assert_eq!(*b.as_ref(), 20);
  }
}

#[test]
fn alloc_inlined_vec() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_inlined(Arena::new(ArenaOptions::new()));
  });

  #[cfg(not(feature = "loom"))]
  alloc_inlined(Arena::new(ArenaOptions::new()));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_inlined_mmap() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_alloc_inlined_mmap");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  alloc_inlined(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_inlined_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE as usize);
  alloc_inlined(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
}

fn alloc_zst(a: Arena) {
  let mut b = unsafe { a.alloc::<()>().unwrap() };

  unsafe {
    assert_eq!(b.as_ref(), &());
    assert_eq!(b.as_mut(), &mut ());
  }

  let mut c = unsafe { a.alloc::<core::marker::PhantomData<Vec<u8>>>().unwrap() };
  unsafe {
    assert_eq!(c.as_ref(), &core::marker::PhantomData::<Vec<u8>>);
    assert_eq!(c.as_mut(), &mut core::marker::PhantomData::<Vec<u8>>);
  }
}

#[test]
fn alloc_zst_vec() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_zst(Arena::new(ArenaOptions::new()));
  });

  #[cfg(not(feature = "loom"))]
  alloc_zst(Arena::new(ArenaOptions::new()));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_zst_mmap() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_alloc_zst_mmap");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE as u64))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  alloc_zst(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_zst_mmap_anon() {
  let mmap_options = MmapOptions::default().len(ARENA_SIZE as usize);
  alloc_zst(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
}
