use core::fmt::Debug;

use super::*;

pub(crate) const RESERVED: u32 = 5;
pub(crate) const DEFAULT_ARENA_OPTIONS: Options = Options::new();

pub(crate) fn run(f: impl Fn() + Send + Sync + 'static) {
  #[cfg(not(feature = "loom"))]
  f();

  #[cfg(feature = "loom")]
  loom::model(f);
}

#[macro_export]
macro_rules! common_unit_tests {
  ($prefix: literal: $ty:ty {
    type Header = $header:ty;
    type SegmentNode = $segment_node:ty;
  }) => {
    const MAX_SEGMENT_NODE_SIZE: u32 = (mem::size_of::<$segment_node>() * 2 - 1) as u32;

    #[test]
    fn test_construct_with_small_capacity_vec() {
      $crate::tests::run(|| $crate::tests::small_capacity_vec::<$ty>(false));
    }

    #[test]
    fn test_construct_with_small_capacity_vec_unify() {
      $crate::tests::run(|| $crate::tests::small_capacity_vec::<$ty>(true));
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn test_construct_with_small_capacity_map_anon() {
      $crate::tests::run(|| $crate::tests::small_capacity_map_anon::<$ty>(false));
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn test_construct_with_small_capacity_map_anon_unify() {
      $crate::tests::run(|| $crate::tests::small_capacity_map_anon::<$ty>(true));
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(miri, ignore)]
    fn test_construct_with_small_capacity_map_mut() {
      $crate::tests::run(|| $crate::tests::small_capacity_map_mut::<$ty>($prefix));
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    #[cfg_attr(miri, ignore)]
    fn test_construct_with_small_capacity_map() {
      $crate::tests::run(|| $crate::tests::small_capacity_map::<$ty>($prefix));
    }

    #[test]
    fn alloc_bytes_vec() {
      $crate::tests::run(|| {
        $crate::tests::alloc_bytes($crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap())
      });
    }

    #[test]
    fn alloc_bytes_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_bytes(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        )
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_bytes_map_anon() {
      $crate::tests::run(|| {
        $crate::tests::alloc_bytes(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .map_anon::<$ty>()
            .unwrap(),
        )
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_bytes_map_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_bytes(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        )
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_bytes_mmap_mut() {
      $crate::tests::run(|| unsafe {
        let dir = ::tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_bytes_mmap", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::alloc_bytes(arena);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn alloc_offset_and_size_vec() {
      $crate::tests::run(|| {
        $crate::tests::alloc_offset_and_size(
          $crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn alloc_offset_and_size_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_offset_and_size(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn alloc_offset_and_size_mmap() {
      $crate::tests::run(|| unsafe {
        let dir = ::tempfile::tempdir().unwrap();
        let p = dir.path().join("test_alloc_offset_and_size_mmap");

        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::alloc_offset_and_size(arena);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn alloc_offset_and_size_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::alloc_offset_and_size(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn alloc_offset_and_size_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_offset_and_size(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    fn alloc_heap_vec() {
      $crate::tests::run(|| {
        $crate::tests::alloc_heap($crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap());
      });
    }

    #[test]
    fn alloc_heap_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_heap(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_heap_mmap_mut() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_alloc_heap_mmap_mut", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::alloc_heap(arena);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_heap_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::alloc_heap(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_heap_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_heap(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    fn alloc_inlined_vec() {
      $crate::tests::run(|| {
        $crate::tests::alloc_inlined($crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap());
      });
    }

    #[test]
    fn alloc_inlined_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_heap(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_inlined_mmap_mut() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_alloc_inlined_mmap", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::alloc_inlined(arena);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_inlined_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::alloc_inlined(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_inlined_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_inlined(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    fn alloc_zst_vec() {
      $crate::tests::run(|| {
        $crate::tests::alloc_zst($crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap());
      });
    }

    #[test]
    fn alloc_zst_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_zst(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_zst_mmap() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_alloc_zst_mmap", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::alloc_zst(arena);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_zst_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::alloc_zst(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn alloc_zst_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::alloc_zst(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    fn carefully_alloc() {
      $crate::tests::run(|| {
        $crate::tests::carefully_alloc(
          $crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap(),
        );
      });
    }

    #[test]
    fn carefully_alloc_unify() {
      $crate::tests::run(|| {
        $crate::tests::carefully_alloc(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn carefully_alloc_mmap() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_carefully_alloc_mmap", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::carefully_alloc(arena);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn carefully_alloc_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::carefully_alloc(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn carefully_alloc_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::carefully_alloc(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn checksum() {
      $crate::tests::run(|| {
        use dbutils::checksum::Crc32;
        use rand::RngCore;

        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_reserved(0)
          .with_capacity(1024 * 1024 * 10)
          .alloc::<$ty>()
          .unwrap();
        let mut buf = arena.alloc_bytes((arena.page_size() * 2) as u32).unwrap();
        buf.set_len(arena.page_size() * 2);
        rand::thread_rng().fill_bytes(&mut buf);

        let cks = Crc32::new();
        let checksum = arena.checksum(&cks);

        assert_eq!(
          checksum,
          Crc32::new().checksum_one(arena.allocated_memory())
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn checksum_with_reserved() {
      $crate::tests::run(|| {
        use dbutils::checksum::Crc32;
        use rand::RngCore;

        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_reserved(5)
          .with_capacity(1024 * 1024 * 10)
          .alloc::<$ty>()
          .unwrap();
        let mut buf = arena.alloc_bytes((arena.page_size() * 2) as u32).unwrap();

        buf.set_len(arena.page_size() * 2);
        rand::thread_rng().fill_bytes(&mut buf);

        let cks = Crc32::new();
        let checksum = arena.checksum(&cks);

        assert_eq!(
          checksum,
          Crc32::new().checksum_one(&arena.allocated_memory()[5..])
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn recoverable() {
      $crate::tests::run(|| {
        $crate::tests::recoverable::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn check_data_offset_vec() {
      $crate::tests::run(|| {
        $crate::tests::check_data_offset(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_reserved($crate::tests::RESERVED)
            .alloc::<$ty>()
            .unwrap(),
          $crate::tests::RESERVED as usize + 1,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn check_data_offset_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::check_data_offset(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .with_reserved($crate::tests::RESERVED)
            .alloc::<$ty>()
            .unwrap(),
          8 + core::mem::size_of::<$header>()
            + $crate::align_offset::<$header>($crate::tests::RESERVED as u32) as usize,
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn check_data_offset_mmap() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_check_data_offset_mmap", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .with_reserved($crate::tests::RESERVED)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::check_data_offset(
          arena,
          8 + core::mem::size_of::<$header>()
            + $crate::align_offset::<$header>($crate::tests::RESERVED as u32) as usize,
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn check_data_offset_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::check_data_offset(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_reserved($crate::tests::RESERVED)
            .alloc::<$ty>()
            .unwrap(),
          $crate::tests::RESERVED as usize + 1,
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn check_data_offset_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::check_data_offset(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_reserved($crate::tests::RESERVED)
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
          8 + core::mem::size_of::<$header>()
            + $crate::align_offset::<$header>($crate::tests::RESERVED as u32) as usize,
        );
      });
    }

    #[cfg(all(not(feature = "loom"), feature = "std"))]
    #[test]
    fn discard_freelist_vec() {
      $crate::tests::run(|| {
        $crate::tests::discard_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap(),
        );
      });
    }

    #[cfg(all(not(feature = "loom"), feature = "std"))]
    #[test]
    fn discard_freelist_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::discard_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn discard_freelist_mmap() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_discard_freelist_mmap", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::discard_freelist(arena);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn discard_freelist_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::discard_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn discard_freelist_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::discard_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn reopen() {
      $crate::tests::run(|| {
        $crate::tests::reopen::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn reopen_with_reserved() {
      $crate::tests::run(|| {
        $crate::tests::reopen_with_reserved::<$ty>($prefix);
      });
    }

    #[test]
    fn with_reserved_vec() {
      $crate::tests::run(|| {
        $crate::tests::with_reserved(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_reserved($crate::tests::RESERVED)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    fn with_reserved_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::with_reserved(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_reserved($crate::tests::RESERVED)
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn with_reserved_map_mut() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir
          .path()
          .join(::std::format!("test_{}_with_reserved_mmap", $prefix));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .with_reserved($crate::tests::RESERVED)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::with_reserved(arena);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn with_reserved_map_anon() {
      $crate::tests::run(|| {
        $crate::tests::with_reserved(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_reserved($crate::tests::RESERVED)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    fn with_reserved_map_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::with_reserved(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_reserved($crate::tests::RESERVED)
            .with_unify(true)
            .map_anon::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn allocate_slow_path_optimistic_vec() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn allocate_slow_path_optimistic_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn allocate_slow_path_optimistic_mmap() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join(::std::format!(
          "test_{}_allocate_slow_path_optimistic_mmap",
          $prefix
        ));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .with_freelist($crate::Freelist::Optimistic)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::allocate_slow_path(arena, MAX_SEGMENT_NODE_SIZE);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn allocate_slow_path_optimistic_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_freelist($crate::Freelist::Optimistic)
            .map_anon::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn allocate_slow_path_optimistic_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .with_freelist($crate::Freelist::Optimistic)
            .map_anon::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn allocate_slow_path_pessimistic_vec() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn allocate_slow_path_pessimistic_vec_unify() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn allocate_slow_path_pessimistic_mmap() {
      $crate::tests::run(|| unsafe {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join(::std::format!(
          "test_{}_allocate_slow_path_pessimistic_mmap",
          $prefix
        ));
        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .with_freelist($crate::Freelist::Pessimistic)
          .map_mut::<$ty, _>(p)
          .unwrap();
        $crate::tests::allocate_slow_path(arena, MAX_SEGMENT_NODE_SIZE);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn allocate_slow_path_pessimistic_mmap_anon() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_freelist($crate::Freelist::Pessimistic)
            .map_anon::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn allocate_slow_path_pessimistic_mmap_anon_unify() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_unify(true)
            .with_freelist($crate::Freelist::Pessimistic)
            .map_anon::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }
  };
}

pub(crate) fn small_capacity_vec<A: Allocator + Debug>(unify: bool) {
  if !unify {
    let e = Options::new()
      .with_capacity(0)
      .with_unify(unify)
      .alloc::<A>()
      .unwrap_err();
    assert!(matches!(e, Error::InsufficientSpace { available: 0, .. }));

    assert!(Options::new()
      .with_capacity(1)
      .with_unify(unify)
      .alloc::<A>()
      .is_ok());

    let e = Options::new()
      .with_capacity(40)
      .with_unify(unify)
      .with_reserved(40)
      .alloc::<A>()
      .unwrap_err();
    assert!(matches!(e, Error::InsufficientSpace { available: 40, .. }));
  } else {
    let e = Options::new()
      .with_capacity(1)
      .with_unify(true)
      .alloc::<A>()
      .unwrap_err();
    assert!(matches!(e, Error::InsufficientSpace { available: 1, .. }));

    let e = Options::new()
      .with_capacity(40)
      .with_reserved(40)
      .with_unify(true)
      .alloc::<A>()
      .unwrap_err();
    assert!(matches!(e, Error::InsufficientSpace { available: 40, .. }));
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub(crate) fn small_capacity_map_anon<A: Allocator + Debug>(unify: bool) {
  if !unify {
    let e = Options::new()
      .with_capacity(0)
      .with_unify(unify)
      .map_anon::<A>()
      .unwrap_err();
    assert!(matches!(e.kind(), std::io::ErrorKind::InvalidInput));
    assert!(Options::new()
      .with_capacity(1)
      .with_unify(unify)
      .map_anon::<A>()
      .is_ok());
  } else {
    let e = Options::new()
      .with_unify(true)
      .with_capacity(1)
      .map_anon::<A>()
      .unwrap_err();
    assert!(matches!(e.kind(), std::io::ErrorKind::InvalidInput));
    assert!(Options::new()
      .with_unify(true)
      .with_capacity(41)
      .map_anon::<A>()
      .is_ok());
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub(crate) fn small_capacity_map_mut<A: Allocator + Debug>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join(format!(
    "test_{prefix}_construct_with_small_capacity_map_mut"
  ));
  let e = unsafe {
    Options::new()
      .with_capacity(1)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(p)
      .unwrap_err()
  };
  assert!(matches!(e.kind(), std::io::ErrorKind::InvalidInput));
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub(crate) fn small_capacity_map<A: Allocator + Debug>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join(format!("test_{prefix}_construct_with_small_capacity_map"));
  let fs = std::fs::OpenOptions::new()
    .create_new(true)
    .write(true)
    .open(&p)
    .unwrap();
  fs.set_len(1).unwrap();
  drop(fs);

  let e = unsafe { Options::new().with_read(true).map::<A, _>(p).unwrap_err() };

  assert!(matches!(e.kind(), std::io::ErrorKind::InvalidData));
}

pub(crate) fn alloc_bytes<A: Allocator>(a: A) {
  let b = a.alloc_bytes(10).unwrap();
  assert_eq!(b.capacity(), 10);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_offset_and_size<A: Allocator>(a: A) {
  use core::marker::PhantomData;

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

pub(crate) fn alloc_heap<A: Allocator>(a: A) {
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

pub(crate) fn alloc_inlined<A: Allocator>(a: A) {
  let mut b = unsafe { a.alloc::<u32>().unwrap() };
  b.write(10);

  unsafe {
    assert_eq!(*b.as_ref(), 10);
    *b.as_mut() = 20;
    assert_eq!(*b.as_ref(), 20);
  }
}

pub(crate) fn alloc_zst<A: Allocator>(a: A) {
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

pub(crate) fn carefully_alloc<A: Allocator>(a: A) {
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

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
pub(crate) fn recoverable<A: Allocator>(prefix: &str) {
  use crate::common::{AtomicU32, Ordering};

  struct Recoverable {
    field1: u64,
    field2: AtomicU32,
  }

  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join(format!("test_{prefix}_alloc_recoverable_mmap"));

  unsafe {
    let offset = {
      let a = DEFAULT_ARENA_OPTIONS
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut::<A, _>(&p)
        .unwrap();
      let mut data = a.alloc::<Recoverable>().unwrap();
      data.write(Recoverable {
        field1: 10,
        field2: AtomicU32::new(20),
      });
      data.detach();
      data.offset()
    };

    let a = DEFAULT_ARENA_OPTIONS
      .with_read(true)
      .map::<A, _>(p)
      .unwrap();
    let data = &*a.get_aligned_pointer::<Recoverable>(offset);
    assert_eq!(data.field1, 10);
    assert_eq!(data.field2.load(Ordering::Relaxed), 20);
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn check_data_offset<A: Allocator>(l: A, offset: usize) {
  let data_offset = l.data_offset();
  assert_eq!(data_offset, offset);

  let b = l.data();
  assert_eq!(b, &[]);
}

#[cfg(all(not(feature = "loom"), feature = "std"))]
pub(crate) fn discard_freelist<A: Allocator>(l: A) {
  let mut allocated = ::std::vec::Vec::new();

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

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn reopen<A: Allocator>(prefix: &str) {
  unsafe {
    let dir = tempfile::tempdir().unwrap();
    let p = dir.path().join(format!("test_{prefix}_reopen"));
    let l = DEFAULT_ARENA_OPTIONS
      .with_create(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();
    let allocated = l.allocated();
    let data_offset = l.data_offset();
    drop(l);

    let l = DEFAULT_ARENA_OPTIONS
      .with_create(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();
    assert_eq!(l.allocated(), allocated);
    assert_eq!(l.data_offset(), data_offset);
    drop(l);

    let l = DEFAULT_ARENA_OPTIONS
      .with_read(true)
      .map::<A, _>(&p)
      .unwrap();
    assert_eq!(l.allocated(), allocated);
    assert_eq!(l.data_offset(), data_offset);
    drop(l);
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn reopen_with_reserved<A: Allocator>(prefix: &str) {
  unsafe {
    let dir = ::tempfile::tempdir().unwrap();
    let p = dir
      .path()
      .join(format!("test_{prefix}_reopen_with_reserved"));

    let l = DEFAULT_ARENA_OPTIONS
      .with_reserved(RESERVED)
      .with_create(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();
    let allocated = l.allocated();
    let data_offset = l.data_offset();

    let reserved_slice = l.reserved_slice_mut();
    for i in 0..RESERVED {
      reserved_slice[i as usize] = i as u8;
    }

    drop(l);

    let l = DEFAULT_ARENA_OPTIONS
      .with_reserved(RESERVED)
      .with_create(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();
    assert_eq!(l.allocated(), allocated);
    assert_eq!(l.data_offset(), data_offset);

    let reserved_slice = l.reserved_slice_mut();
    for i in 0..RESERVED {
      assert_eq!(reserved_slice[i as usize], i as u8);
      reserved_slice[i as usize] += 1;
    }

    drop(l);

    let l = DEFAULT_ARENA_OPTIONS
      .with_reserved(RESERVED)
      .with_read(true)
      .map::<A, _>(&p)
      .unwrap();
    assert_eq!(l.allocated(), allocated);
    assert_eq!(l.data_offset(), data_offset);

    let reserved_slice = l.reserved_slice();
    for i in 0..RESERVED {
      assert_eq!(reserved_slice[i as usize], i as u8 + 1);
    }

    drop(l);
  }
}

pub(crate) fn with_reserved<A: Allocator>(l: A) {
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

#[cfg(not(feature = "loom"))]
pub(crate) fn allocate_slow_path<A: Allocator>(l: A, max_segment_node_size: u32) {
  // make some segments
  for i in 1..=5 {
    let _ = l.alloc_bytes(i * 50).unwrap();
  }

  let remaining = l.remaining();
  let _ = l.alloc_bytes(remaining as u32).unwrap();

  // 751 -> 501 -> 301 -> 151 -> 51 -> 1

  // allocate from segments
  for i in (1..=5).rev() {
    l.alloc_bytes(i * 50 - max_segment_node_size).unwrap();
  }
}
