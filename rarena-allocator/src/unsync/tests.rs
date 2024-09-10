#![allow(dead_code)]

use core::marker::PhantomData;

use crate::Memory as _;

use super::*;

mod optimistic_slow_path;
mod pessimistic_slow_path;

const ARENA_SIZE: u32 = 1024;
const MAX_SEGMENT_NODE_SIZE: u32 = (SEGMENT_NODE_SIZE * 2 - 1) as u32;

#[cfg(not(feature = "reserved"))]
const RESERVED: u32 = 0;
#[cfg(feature = "reserved")]
const RESERVED: u32 = 5;
const DEFAULT_ARENA_OPTIONS: ArenaOptions = ArenaOptions::new().with_reserved(RESERVED);

fn run(f: impl Fn() + Send + Sync + 'static) {
  #[cfg(not(feature = "loom"))]
  f();

  #[cfg(feature = "loom")]
  loom::model(f);
}

#[test]
fn test_meta_eq() {
  let a_ptr = 1u8;
  let b_ptr = 1u8;
  let a = Meta::new(&a_ptr as _, 2, 3);
  let b = Meta::new(&b_ptr as _, 2, 3);
  assert_ne!(a, b);
}

fn alloc_bytes(a: Arena) {
  let b = a.alloc_bytes(10).unwrap();
  assert_eq!(b.capacity(), 10);
}

#[test]
fn alloc_bytes_vec() {
  run(|| alloc_bytes(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap()))
}

#[test]
fn alloc_bytes_vec_unify() {
  run(|| alloc_bytes(Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap()))
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_bytes_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_bytes_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_bytes(Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_bytes_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_bytes(Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_bytes_mmap_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_bytes(Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_unify(true), mmap_options).unwrap());
  });
}

fn alloc_offset_and_size(a: Arena) {
  #[derive(Debug)]
  #[repr(C)]
  struct Meta {
    /// The maximum MVCC version of the skiplist. CAS.
    max_version: u64,
    /// The minimum MVCC version of the skiplist. CAS.
    min_version: u64,
    /// Current height. 1 <= height <= kMaxHeight. CAS.
    height: u32,
    len: u32,
  }

  #[repr(C)]
  struct Node<T> {
    value: u64,
    key_offset: u32,
    key_size_and_height: u32,
    trailer: PhantomData<T>,
  }

  #[derive(Debug)]
  #[repr(C)]
  struct Link {
    next_offset: u32,
    prev_offset: u32,
  }

  let offset = a.data_offset();
  let alignment = mem::align_of::<Meta>();
  let meta_offset = (offset + alignment - 1) & !(alignment - 1);
  let meta_end = meta_offset + mem::size_of::<Meta>();

  let meta = unsafe { a.alloc::<Meta>().unwrap() };
  assert_eq!(meta.offset(), meta_offset);
  assert_eq!(meta.capacity() + meta.offset(), meta_end);

  let head = a
    .alloc_aligned_bytes::<Node<u64>>(20 * mem::size_of::<Link>() as u32)
    .unwrap();
  assert_eq!(head.offset(), meta_end);
}

#[test]
#[cfg(not(feature = "loom"))]
fn alloc_offset_and_size_vec() {
  run(|| {
    alloc_offset_and_size(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap());
  });
}

#[test]
#[cfg(not(feature = "loom"))]
fn alloc_offset_and_size_vec_unify() {
  run(|| {
    alloc_offset_and_size(Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_offset_and_size_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_offset_and_size_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_offset_and_size(
      Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn alloc_offset_and_size_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_offset_and_size(Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap());
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
  run(|| {
    alloc_heap(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap());
  });
}

#[test]
fn alloc_heap_vec_unify() {
  run(|| {
    alloc_heap(Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_heap_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_heap_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_heap(Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_heap_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_heap(Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_heap_mmap_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_heap(Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_unify(true), mmap_options).unwrap());
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
  run(|| {
    alloc_inlined(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap());
  });
}

#[test]
fn alloc_inlined_vec_unify() {
  run(|| {
    alloc_inlined(Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_inlined_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_inlined_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_inlined(Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_inlined_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_inlined(Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_inlined_mmap_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_inlined(Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_unify(true), mmap_options).unwrap());
  });
}

fn alloc_zst(a: Arena) {
  {
    let mut b = unsafe { a.alloc::<()>().unwrap() };

    unsafe {
      assert_eq!(b.as_ref(), &());
      assert_eq!(b.as_mut(), &mut ());
    }
  }

  let mut c = unsafe { a.alloc::<core::marker::PhantomData<Vec<u8>>>().unwrap() };
  unsafe {
    assert_eq!(c.as_ref(), &core::marker::PhantomData::<Vec<u8>>);
    assert_eq!(c.as_mut(), &mut core::marker::PhantomData::<Vec<u8>>);
  }
}

#[test]
fn alloc_zst_vec() {
  run(|| {
    alloc_zst(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap());
  });
}

#[test]
fn alloc_zst_vec_unify() {
  run(|| {
    alloc_zst(Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_zst_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_alloc_zst_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    alloc_zst(Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_zst_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_zst(Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn alloc_zst_mmap_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    alloc_zst(Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_unify(true), mmap_options).unwrap());
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
  run(|| {
    carefully_alloc_in(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap());
  });
}

#[test]
fn carefully_alloc_unify() {
  run(|| {
    carefully_alloc_in(Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn carefully_alloc_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_carefully_alloc_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    carefully_alloc_in(
      Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn carefully_alloc_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    carefully_alloc_in(Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn carefully_alloc_mmap_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    carefully_alloc_in(
      Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_unify(true), mmap_options).unwrap(),
    );
  });
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
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
      let a = Arena::map_mut(&p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap();
      let mut data = a.alloc::<Recoverable>().unwrap();
      data.write(Recoverable {
        field1: 10,
        field2: AtomicU32::new(20),
      });
      data.detach();
      data.offset()
    };

    let a = Arena::map(
      p,
      DEFAULT_ARENA_OPTIONS,
      OpenOptions::new().read(true),
      MmapOptions::default(),
    )
    .unwrap();
    let data = &*a.get_aligned_pointer::<Recoverable>(offset);
    assert_eq!(data.field1, 10);
    assert_eq!(data.field2.load(Ordering::Relaxed), 20);
  }
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn recoverable() {
  run(|| {
    recoverable_in();
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn test_too_small() {
  use crate::error::TooSmall;

  let too_small = TooSmall::new(10, 20);
  assert_eq!(
    std::format!("{}", too_small),
    "memmap size is less than the minimum capacity: 10 < 20"
  );
}

#[cfg(not(feature = "loom"))]
fn check_data_offset(l: Arena, offset: usize) {
  let data_offset = l.data_offset();
  assert_eq!(data_offset, offset);

  let b = l.data();
  assert_eq!(b, &[]);
}

#[test]
#[cfg(not(feature = "loom"))]
fn check_data_offset_vec() {
  run(|| {
    check_data_offset(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap(), RESERVED as usize + 1);
  });
}

#[test]
#[cfg(not(feature = "loom"))]
fn check_data_offset_vec_unify() {
  run(|| {
    check_data_offset(
      Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap(),
      8 + core::mem::size_of::<super::Header>()
        + crate::align_offset::<super::Header>(RESERVED as u32) as usize,
    );
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn check_data_offset_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_check_data_offset_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    check_data_offset(
      Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap(),
      8 + core::mem::size_of::<super::Header>()
        + crate::align_offset::<super::Header>(RESERVED as u32) as usize,
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn check_data_offset_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    check_data_offset(
      Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap(),
      RESERVED as usize + 1,
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn check_data_offset_mmap_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    check_data_offset(
      Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_unify(true), mmap_options).unwrap(),
      8 + core::mem::size_of::<super::Header>()
        + crate::align_offset::<super::Header>(RESERVED as u32) as usize,
    );
  });
}

#[cfg(all(not(feature = "loom"), feature = "std"))]
fn discard_freelist_in(l: Arena) {
  let mut allocated = std::vec::Vec::new();

  // make some segments
  for i in 1..=5 {
    let bytes = l.alloc_bytes_owned(i * 50).unwrap();
    let _ = allocated.push(bytes);
  }

  let remaining = l.remaining();
  let mut remaining = l.alloc_bytes(remaining as u32).unwrap();
  unsafe {
    remaining.detach();
  }
  drop(allocated);

  l.discard_freelist().unwrap();
}

#[cfg(all(not(feature = "loom"), feature = "std"))]
#[test]
fn discard_freelist() {
  run(|| {
    discard_freelist_in(Arena::new(DEFAULT_ARENA_OPTIONS).unwrap());
  });
}

#[cfg(all(not(feature = "loom"), feature = "std"))]
#[test]
fn discard_freelist_unify() {
  run(|| {
    discard_freelist_in(Arena::new(DEFAULT_ARENA_OPTIONS.with_unify(true)).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn discard_freelist_mmap() {
  run(|| {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join("test_discard_freelist_mmap");
    let open_options = OpenOptions::default()
      .create_new(Some(ARENA_SIZE))
      .read(true)
      .write(true);
    let mmap_options = MmapOptions::default();
    discard_freelist_in(
      Arena::map_mut(p, DEFAULT_ARENA_OPTIONS, open_options, mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn discard_freelist_mmap_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    discard_freelist_in(Arena::map_anon(DEFAULT_ARENA_OPTIONS, mmap_options).unwrap());
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn discard_freelist_mmap_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    discard_freelist_in(
      Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_unify(true), mmap_options).unwrap(),
    );
  });
}

#[cfg(not(feature = "loom"))]
fn allocate_slow_path(l: Arena) {
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
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn reopen() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_reopen");
  let open_options = OpenOptions::default()
    .create(Some(ARENA_SIZE))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  let l = Arena::map_mut(
    p.clone(),
    DEFAULT_ARENA_OPTIONS,
    open_options.clone(),
    mmap_options.clone(),
  )
  .unwrap();
  let allocated = l.allocated();
  let data_offset = l.data_offset();
  drop(l);

  let l = Arena::map_mut(
    p.clone(),
    DEFAULT_ARENA_OPTIONS,
    open_options,
    mmap_options.clone(),
  )
  .unwrap();
  assert_eq!(l.allocated(), allocated);
  assert_eq!(l.data_offset(), data_offset);
  drop(l);

  let l = Arena::map(
    p.clone(),
    DEFAULT_ARENA_OPTIONS,
    OpenOptions::new().read(true),
    mmap_options,
  )
  .unwrap();
  assert_eq!(l.allocated(), allocated);
  assert_eq!(l.data_offset(), data_offset);
  drop(l);
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
fn reopen_with_reserved() {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_reopen");
  let open_options = OpenOptions::default()
    .create(Some(ARENA_SIZE))
    .read(true)
    .write(true);
  let mmap_options = MmapOptions::default();
  let l = Arena::map_mut(
    p.clone(),
    DEFAULT_ARENA_OPTIONS.with_reserved(RESERVED),
    open_options.clone(),
    mmap_options.clone(),
  )
  .unwrap();
  let allocated = l.allocated();
  let data_offset = l.data_offset();
  unsafe {
    let reserved_slice = l.reserved_slice_mut();
    for i in 0..RESERVED {
      reserved_slice[i as usize] = i as u8;
    }
  }

  drop(l);

  let l = Arena::map_mut(
    p.clone(),
    DEFAULT_ARENA_OPTIONS,
    open_options,
    mmap_options.clone(),
  )
  .unwrap();
  assert_eq!(l.allocated(), allocated);
  assert_eq!(l.data_offset(), data_offset);

  unsafe {
    let reserved_slice = l.reserved_slice_mut();
    for i in 0..RESERVED {
      assert_eq!(reserved_slice[i as usize], i as u8);
      reserved_slice[i as usize] += 1;
    }
  }
  drop(l);

  let l = Arena::map(
    p.clone(),
    DEFAULT_ARENA_OPTIONS.with_reserved(RESERVED),
    OpenOptions::new().read(true),
    mmap_options,
  )
  .unwrap();
  assert_eq!(l.allocated(), allocated);
  assert_eq!(l.data_offset(), data_offset);

  let reserved_slice = l.reserved_slice();
  for i in 0..RESERVED {
    assert_eq!(reserved_slice[i as usize], i as u8 + 1);
  }

  drop(l);
}

fn with_reserved(l: Arena) {
  unsafe {
    let reserved_slice = l.reserved_slice_mut();
    for i in 0..RESERVED {
      reserved_slice[i as usize] = i as u8;
    }
  }

  let mut b = l.alloc_bytes(10).unwrap();

  unsafe {
    let reserved_slice = l.reserved_slice();
    for i in 0..RESERVED {
      assert_eq!(reserved_slice[i as usize], i as u8);
    }

    b.detach();
  }
}

#[test]
fn with_reserved_vec() {
  run(|| {
    with_reserved(Arena::new(DEFAULT_ARENA_OPTIONS.with_reserved(RESERVED)).unwrap());
  });
}

#[test]
fn with_reserved_vec_unify() {
  run(|| {
    with_reserved(Arena::new(
      DEFAULT_ARENA_OPTIONS
        .with_unify(true)
        .with_reserved(RESERVED),
    ).unwrap());
  });
}

#[test]
#[cfg_attr(miri, ignore)]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn with_reserved_map_anon() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    with_reserved(
      Arena::map_anon(DEFAULT_ARENA_OPTIONS.with_reserved(RESERVED), mmap_options).unwrap(),
    );
  });
}

#[test]
#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
fn with_reserved_map_anon_unify() {
  run(|| {
    let mmap_options = MmapOptions::default().len(ARENA_SIZE);
    with_reserved(
      Arena::map_anon(
        DEFAULT_ARENA_OPTIONS
          .with_unify(true)
          .with_reserved(RESERVED),
        mmap_options,
      )
      .unwrap(),
    );
  });
}
