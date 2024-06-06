#![allow(dead_code)]

use super::*;

const ARENA_SIZE: u32 = 1024;

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
fn alloc_bytes_vec_unify() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_bytes(Arena::new(ArenaOptions::new().with_unify(true)));
  });

  #[cfg(not(feature = "loom"))]
  alloc_bytes(Arena::new(ArenaOptions::new().with_unify(true)));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_bytes_mmap() {
  #[cfg(not(feature = "loom"))]
  {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_bytes_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_bytes(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_bytes_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_bytes(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_bytes_mmap_anon() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_bytes(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_bytes(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_bytes_mmap_anon_unify() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_bytes(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_bytes(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  });
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
fn alloc_heap_vec_unify() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_heap(Arena::new(ArenaOptions::new().with_unify(true)));
  });

  #[cfg(not(feature = "loom"))]
  alloc_heap(Arena::new(ArenaOptions::new().with_unify(true)));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_heap_mmap() {
  #[cfg(not(feature = "loom"))]
  {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_heap_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_heap(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_heap_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_heap(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_heap_mmap_anon() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_heap(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_heap(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_heap_mmap_anon_unify() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_heap(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_heap(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  });
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
fn alloc_inlined_vec_unify() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_inlined(Arena::new(ArenaOptions::new().with_unify(true)));
  });

  #[cfg(not(feature = "loom"))]
  alloc_inlined(Arena::new(ArenaOptions::new().with_unify(true)));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_inlined_mmap() {
  #[cfg(not(feature = "loom"))]
  {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_inlined_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_inlined(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_inlined_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_inlined(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_inlined_mmap_anon() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_inlined(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_inlined(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_inlined_mmap_anon_unify() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_inlined(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_inlined(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  });
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
fn alloc_zst_vec_unify() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    alloc_zst(Arena::new(ArenaOptions::new().with_unify(true)));
  });

  #[cfg(not(feature = "loom"))]
  alloc_zst(Arena::new(ArenaOptions::new().with_unify(true)));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_zst_mmap() {
  #[cfg(not(feature = "loom"))]
  {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_zst_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_zst(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_zst_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_zst(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_zst_mmap_anon() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_zst(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_zst(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_zst_mmap_anon_unify() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_zst(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_zst(Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap());
  });
}

fn carefully_alloc_in(a: Arena) {
  unsafe {
    {
      let mut data = a.alloc::<Vec<u8>>().unwrap();
      data.write(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    }

    let mut data = a.alloc::<Vec<u8>>().unwrap();
    data.detach();
    data.write(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);

    core::ptr::drop_in_place(data.as_mut());
  }
}

#[test]
fn carefully_alloc() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    carefully_alloc_in(Arena::new(ArenaOptions::new()));
  });

  #[cfg(not(feature = "loom"))]
  carefully_alloc_in(Arena::new(ArenaOptions::new()));
}

#[test]
fn carefully_alloc_unify() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    carefully_alloc_in(Arena::new(ArenaOptions::new().with_unify(true)));
  });

  #[cfg(not(feature = "loom"))]
  carefully_alloc_in(Arena::new(ArenaOptions::new().with_unify(true)));
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn carefully_alloc_mmap() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_carefully_alloc_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    carefully_alloc_in(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  });

  #[cfg(not(feature = "loom"))]
  {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_carefully_alloc_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    carefully_alloc_in(Arena::map_mut(p, ArenaOptions::new(), open_options, mmap_options).unwrap());
  }
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn carefully_alloc_mmap_anon() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    carefully_alloc_in(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    carefully_alloc_in(Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn carefully_alloc_mmap_anon_unify() {
  #[cfg(not(feature = "loom"))]
  {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    carefully_alloc_in(
      Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap(),
    );
  }

  #[cfg(feature = "loom")]
  loom::model(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    carefully_alloc_in(
      Arena::map_anon(ArenaOptions::new().with_unify(true), mmap_options).unwrap(),
    );
  });
}

fn recoverable_in() {
  struct Recoverable {
    field1: u64,
    field2: AtomicU32,
  }

  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_alloc_recoverable_mmap");
  let open_options = OpenOptions::default()
    .create_new(Some(ARENA_SIZE))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();

  unsafe {
    let offset = {
      let a = Arena::map_mut(&p, ArenaOptions::new(), open_options, mmap_options).unwrap();
      let mut data = a.alloc::<Recoverable>().unwrap();
      data.write(Recoverable {
        field1: 10,
        field2: AtomicU32::new(20),
      });
      data.offset()
    };

    let a = Arena::map(p, OpenOptions::new().read(true), MmapOptions::default()).unwrap();
    let data = &*a.get_aligned_pointer::<Recoverable>(offset);
    assert_eq!(data.field1, 10);
    assert_eq!(data.field2.load(Ordering::Relaxed), 20);
  }
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn recoverable() {
  #[cfg(feature = "loom")]
  loom::model(|| {
    recoverable_in();
  });

  #[cfg(not(feature = "loom"))]
  recoverable_in();
}
