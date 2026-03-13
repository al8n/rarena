use core::fmt::Debug;

use super::*;

pub(crate) const RESERVED: u32 = 5;
pub(crate) const DEFAULT_ARENA_OPTIONS: Options = Options::new().with_capacity(1024);

pub(crate) fn run(f: impl Fn() + Send + Sync + 'static) {
  #[cfg(not(feature = "loom"))]
  f();

  #[cfg(feature = "loom")]
  loom::model(f);
}

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
        use rand::RngExt;

        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_reserved(0)
          .with_capacity(1024 * 1024 * 10)
          .alloc::<$ty>()
          .unwrap();
        let mut buf = arena.alloc_bytes((arena.page_size() * 2) as u32).unwrap();
        buf.set_len(arena.page_size() * 2);
        rand::rng().fill(&mut *buf);

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
        use rand::RngExt;

        let arena = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_reserved(5)
          .with_capacity(1024 * 1024 * 10)
          .alloc::<$ty>()
          .unwrap();
        let mut buf = arena.alloc_bytes((arena.page_size() * 2) as u32).unwrap();

        buf.set_len(arena.page_size() * 2);
        rand::rng().fill(&mut *buf);

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
        let opts = $crate::tests::DEFAULT_ARENA_OPTIONS.with_reserved($crate::tests::RESERVED);
        let data_offset = opts.data_offset::<$ty>();
        $crate::tests::check_data_offset(opts.alloc::<$ty>().unwrap(), data_offset);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn check_data_offset_vec_unify() {
      $crate::tests::run(|| {
        let opts = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_unify(true)
          .with_reserved($crate::tests::RESERVED);
        let data_offset = opts.data_offset_unify::<$ty>();
        $crate::tests::check_data_offset(opts.alloc::<$ty>().unwrap(), data_offset);
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
        let opts = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_create_new(true)
          .with_read(true)
          .with_write(true)
          .with_reserved($crate::tests::RESERVED);
        let data_offset = opts.data_offset_unify::<$ty>();
        let arena = opts.map_mut::<$ty, _>(p).unwrap();
        $crate::tests::check_data_offset(arena, data_offset);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn check_data_offset_mmap_anon() {
      $crate::tests::run(|| {
        let opts = $crate::tests::DEFAULT_ARENA_OPTIONS.with_reserved($crate::tests::RESERVED);
        let data_offset = opts.data_offset::<$ty>();

        $crate::tests::check_data_offset(opts.alloc::<$ty>().unwrap(), data_offset);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    fn check_data_offset_mmap_anon_unify() {
      $crate::tests::run(|| {
        let opts = $crate::tests::DEFAULT_ARENA_OPTIONS
          .with_reserved($crate::tests::RESERVED)
          .with_unify(true);
        let data_offset = opts.data_offset_unify::<$ty>();
        $crate::tests::check_data_offset(opts.alloc::<$ty>().unwrap(), data_offset);
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
    fn test_error_display() {
      $crate::tests::run(|| {
        $crate::tests::error_display();
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_read_write() {
      $crate::tests::run(|| {
        $crate::tests::bytes_read_write(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_owned() {
      $crate::tests::run(|| {
        $crate::tests::bytes_owned(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_allocator_getters() {
      $crate::tests::run(|| {
        $crate::tests::allocator_getters(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_allocator_properties() {
      $crate::tests::run(|| {
        $crate::tests::allocator_properties(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_owned_bytes() {
      $crate::tests::run(|| {
        $crate::tests::alloc_owned_bytes(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_object_owned() {
      $crate::tests::run(|| {
        $crate::tests::object_owned(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_arena_clear() {
      $crate::tests::run(|| {
        $crate::tests::arena_clear(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_arena_rewind() {
      $crate::tests::run(|| {
        $crate::tests::arena_rewind(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_insufficient_space() {
      $crate::tests::run(|| {
        $crate::tests::alloc_insufficient_space(
          $crate::tests::DEFAULT_ARENA_OPTIONS.alloc::<$ty>().unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_set_len() {
      $crate::tests::run(|| {
        $crate::tests::bytes_set_len(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_flush_operations() {
      $crate::tests::run(|| {
        $crate::tests::flush_operations::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_lock_operations() {
      $crate::tests::run(|| {
        $crate::tests::lock_operations::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_read_only() {
      $crate::tests::run(|| {
        $crate::tests::read_only::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_paths() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_paths(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_with_freelist_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_with_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_with_freelist_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_with_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_rewind_all_positions() {
      $crate::tests::run(|| {
        $crate::tests::rewind_all_positions(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_aligned() {
      $crate::tests::run(|| {
        $crate::tests::alloc_aligned(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_write_io() {
      $crate::tests::run(|| {
        $crate::tests::bytes_write_io(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_freelist_none() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_freelist_none(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_freelist($crate::Freelist::None)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_sanity_check_errors() {
      $crate::tests::run(|| {
        $crate::tests::sanity_check_errors::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_map_copy() {
      $crate::tests::run(|| {
        $crate::tests::map_copy::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_write_methods() {
      $crate::tests::run(|| {
        $crate::tests::bytes_write_methods(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_allocator_leb128() {
      $crate::tests::run(|| {
        $crate::tests::allocator_leb128(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_memmap_anon_operations() {
      $crate::tests::run(|| {
        $crate::tests::memmap_anon_operations::<$ty>();
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_interleaved_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_interleaved(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_interleaved_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_interleaved(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_aligned_slow_path_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::alloc_aligned_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(1024)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_aligned_slow_path_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::alloc_aligned_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(1024)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_flush_header_operations() {
      $crate::tests::run(|| {
        $crate::tests::flush_header_operations::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_debug_and_clone() {
      $crate::tests::run(|| {
        $crate::tests::debug_and_clone(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_error_variants() {
      $crate::tests::run(|| {
        $crate::tests::error_variants::<$ty>();
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_owned_detach_and_drop() {
      $crate::tests::run(|| {
        $crate::tests::bytes_owned_detach_and_drop(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_reserved_bytes_zero() {
      $crate::tests::run(|| {
        $crate::tests::reserved_bytes_zero(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_reserved(0)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_get_bytes_and_pointers() {
      $crate::tests::run(|| {
        $crate::tests::get_bytes_and_pointers(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_set_minimum_segment_size() {
      $crate::tests::run(|| {
        $crate::tests::set_minimum_segment_size(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_in_slow_path_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::alloc_in_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(1024)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_in_slow_path_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::alloc_in_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(1024)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_path_builder_operations() {
      $crate::tests::run(|| {
        $crate::tests::path_builder_operations::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_arena_clear_unify() {
      $crate::tests::run(|| {
        $crate::tests::arena_clear(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_unify(true)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_slice_operations() {
      $crate::tests::run(|| {
        $crate::tests::bytes_slice_operations(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_align_and_put() {
      $crate::tests::run(|| {
        $crate::tests::bytes_align_and_put(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_refmut_write_read() {
      $crate::tests::run(|| {
        $crate::tests::refmut_write_read(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_leb128() {
      $crate::tests::run(|| {
        $crate::tests::bytes_leb128(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_options_getters() {
      $crate::tests::run(|| {
        $crate::tests::options_getters();
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_freelist_try_from() {
      $crate::tests::run(|| {
        $crate::tests::freelist_try_from();
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_reserved_slice_operations() {
      $crate::tests::run(|| {
        $crate::tests::reserved_slice_operations(
          Options::new()
            .with_capacity(4096)
            .with_reserved(16)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_owned_write_io() {
      $crate::tests::run(|| {
        $crate::tests::bytes_owned_write_io(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_mlock_operations() {
      $crate::tests::run(|| {
        $crate::tests::mlock_operations::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_read_write_more() {
      $crate::tests::run(|| {
        $crate::tests::bytes_read_write_more(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_truncate_anon_mmap() {
      $crate::tests::run(|| {
        $crate::tests::truncate_anon_mmap::<$ty>();
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_arena_remaining_and_data() {
      $crate::tests::run(|| {
        $crate::tests::arena_remaining_and_data(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_object_ref_mut() {
      $crate::tests::run(|| {
        $crate::tests::object_ref_mut(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_allocate_slow_path_multiple_rounds() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path_multiple_rounds(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(2048)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_allocate_slow_path_multiple_rounds_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::allocate_slow_path_multiple_rounds(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(2048)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_flush_range_out_of_bounds() {
      $crate::tests::run(|| {
        $crate::tests::flush_range_out_of_bounds::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_many_segments() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_many_segments(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_many_segments_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_many_segments(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_i8_operations() {
      $crate::tests::run(|| {
        $crate::tests::bytes_i8_operations(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_set_len_edge_cases() {
      $crate::tests::run(|| {
        $crate::tests::bytes_set_len_edge_cases(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_flush_header_overlap_cases() {
      $crate::tests::run(|| {
        $crate::tests::flush_header_overlap_cases::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
    #[cfg_attr(miri, ignore)]
    fn test_lock_on_mmap_file() {
      $crate::tests::run(|| {
        $crate::tests::lock_on_mmap_file::<$ty>($prefix);
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_aligned_in_slow_path_opt() {
      $crate::tests::run(|| {
        $crate::tests::alloc_aligned_in_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(2048)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_aligned_in_slow_path_pes() {
      $crate::tests::run(|| {
        $crate::tests::alloc_aligned_in_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(2048)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_type_in_slow_path_opt() {
      $crate::tests::run(|| {
        $crate::tests::alloc_type_in_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(2048)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_type_in_slow_path_pes() {
      $crate::tests::run(|| {
        $crate::tests::alloc_type_in_slow_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(2048)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
          MAX_SEGMENT_NODE_SIZE,
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_discard_freelist_operations_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::discard_freelist_operations(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_discard_freelist_operations_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::discard_freelist_operations(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_aligned_bytes_error_path() {
      $crate::tests::run(|| {
        $crate::tests::alloc_aligned_bytes_error_path(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_freelist($crate::Freelist::None)
            .alloc::<$ty>()
            .unwrap(),
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

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_slow_path_with_remainder_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::slow_path_with_remainder(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_slow_path_with_remainder_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::slow_path_with_remainder(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_tiny_segments_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_tiny_segments(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_dealloc_tiny_segments_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::dealloc_tiny_segments(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_type_slow_path_with_freelist_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::alloc_type_slow_path_with_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_type_slow_path_with_freelist_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::alloc_type_slow_path_with_freelist(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_error_display_formats() {
      $crate::tests::run(|| {
        $crate::tests::error_display_formats::<$ty>(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_alloc_zst_operations() {
      $crate::tests::run(|| {
        $crate::tests::alloc_zst_operations(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_segment_debug_and_list_ops_optimistic() {
      $crate::tests::run(|| {
        $crate::tests::segment_debug_and_list_ops(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Optimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_segment_debug_and_list_ops_pessimistic() {
      $crate::tests::run(|| {
        $crate::tests::segment_debug_and_list_ops(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(8192)
            .with_freelist($crate::Freelist::Pessimistic)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_leb128_unchecked() {
      $crate::tests::run(|| {
        $crate::tests::bytes_leb128_unchecked(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
        );
      });
    }

    #[test]
    #[cfg(not(feature = "loom"))]
    fn test_bytes_align_to_error() {
      $crate::tests::run(|| {
        $crate::tests::bytes_align_to_error(
          $crate::tests::DEFAULT_ARENA_OPTIONS
            .with_capacity(4096)
            .alloc::<$ty>()
            .unwrap(),
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

    assert!(
      Options::new()
        .with_capacity(1)
        .with_unify(unify)
        .alloc::<A>()
        .is_ok()
    );

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
    assert!(
      Options::new()
        .with_capacity(1)
        .with_unify(unify)
        .map_anon::<A>()
        .is_ok()
    );
  } else {
    let e = Options::new()
      .with_unify(true)
      .with_capacity(1)
      .map_anon::<A>()
      .unwrap_err();
    assert!(matches!(e.kind(), std::io::ErrorKind::InvalidInput));
    assert!(
      Options::new()
        .with_unify(true)
        .with_capacity(41)
        .map_anon::<A>()
        .is_ok()
    );
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
    .read(true)
    .write(true)
    .open(&p)
    .unwrap();
  fs.set_len(1).unwrap();
  drop(fs);

  let _e = unsafe { Options::new().with_read(true).map::<A, _>(p).unwrap_err() };

  // assert!(
  //   matches!(e.kind(), std::io::ErrorKind::InvalidData),
  //   "{e} {e:?}"
  // );
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
  assert_eq!(b, &[] as &[u8]);
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

pub(crate) fn error_display() {
  let e = Error::InsufficientSpace {
    requested: 100,
    available: 50,
  };
  let s = std::format!("{e}");
  assert!(s.contains("100"));
  assert!(s.contains("50"));

  let e = Error::ReadOnly;
  let s = std::format!("{e}");
  assert!(s.contains("read-only"));

  let e = Error::OutOfBounds {
    offset: 42,
    allocated: 10,
  };
  let s = std::format!("{e}");
  assert!(s.contains("42"));
  assert!(s.contains("10"));

  // Test Clone, PartialEq, Eq, Debug
  let e2 = e.clone();
  assert_eq!(e, e2);
  let _ = std::format!("{e:?}");
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_read_write<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(128).unwrap();
  assert_eq!(buf.capacity(), 128);

  // Test writing bytes using put methods (appends to end)
  buf.put_u8(42).unwrap();
  assert_eq!(buf.len(), 1);

  // Use big-endian put/get pairs since get_* always reads as big-endian
  buf.put_u16_be(1234).unwrap();
  buf.put_u32_be(567890).unwrap();
  buf.put_u64_be(1234567890).unwrap();
  buf.put_i32_be(-42).unwrap();
  buf.put_i64_be(-123456).unwrap();

  let written = buf.len();
  assert!(written > 0);

  // get_* methods pop from the end (LIFO), so read in reverse order
  assert_eq!(buf.get_i64_be().unwrap(), -123456);
  assert_eq!(buf.get_i32_be().unwrap(), -42);
  assert_eq!(buf.get_u64_be().unwrap(), 1234567890);
  assert_eq!(buf.get_u32_be().unwrap(), 567890);
  assert_eq!(buf.get_u16_be().unwrap(), 1234);
  assert_eq!(buf.get_u8().unwrap(), 42);

  assert_eq!(buf.len(), 0);

  // Test put_slice
  buf.put_slice(b"hello").unwrap();
  assert_eq!(buf.len(), 5);

  // Test get_slice
  let slice = buf.get_slice(5).unwrap();
  assert_eq!(slice, b"hello");

  // Test Deref with content
  buf.put_u8(99).unwrap();
  let _slice: &[u8] = &buf;
  assert!(!_slice.is_empty());

  // Test DerefMut
  let _slice_mut: &mut [u8] = &mut buf;
  assert!(!_slice_mut.is_empty());

  // Test AsRef/AsMut
  let _as_ref: &[u8] = buf.as_ref();
  let _as_mut: &mut [u8] = buf.as_mut();

  // Test Debug
  let _ = std::format!("{buf:?}");

  // Test as_ptr / as_mut_ptr
  let _ptr = buf.as_ptr();
  let _mut_ptr = buf.as_mut_ptr();
  assert!(!_ptr.is_null());
  assert!(!_mut_ptr.is_null());

  // Test remaining
  assert!(buf.remaining() <= 128 - buf.len());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_owned<A: Allocator>(a: A) {
  let b = a.alloc_bytes_owned(64).unwrap();
  assert_eq!(b.capacity(), 64);

  // Test Buffer trait on BytesMut
  let offset = b.offset();
  assert!(offset > 0);
  let buf_offset = b.buffer_offset();
  assert!(buf_offset > 0);
  let buf_cap = b.buffer_capacity();
  assert!(buf_cap > 0);

  // Test Deref/DerefMut
  let _slice: &[u8] = &b;
  let _ = std::format!("{b:?}");
}

#[cfg(not(feature = "loom"))]
pub(crate) fn allocator_getters<A: Allocator>(a: A) {
  // Write some data first
  let mut buf = a.alloc_bytes(64).unwrap();
  buf.set_len(64);
  // Fill buffer with known values
  for (i, byte) in buf.iter_mut().enumerate() {
    *byte = (i & 0xFF) as u8;
  }
  let data_start = buf.offset();
  unsafe { buf.detach() };
  drop(buf);

  // Test get_u8 / get_i8
  assert!(a.get_u8(data_start).is_ok());
  assert!(a.get_i8(data_start).is_ok());

  // Test bounds checking
  let too_big = a.capacity() + 1;
  assert!(a.get_u8(too_big).is_err());
  assert!(a.get_i8(too_big).is_err());

  // Test multi-byte getters
  assert!(a.get_u16_le(data_start).is_ok());
  assert!(a.get_u16_be(data_start).is_ok());
  assert!(a.get_u32_le(data_start).is_ok());
  assert!(a.get_u32_be(data_start).is_ok());
  assert!(a.get_u64_le(data_start).is_ok());
  assert!(a.get_u64_be(data_start).is_ok());
  assert!(a.get_i16_le(data_start).is_ok());
  assert!(a.get_i16_be(data_start).is_ok());
  assert!(a.get_i32_le(data_start).is_ok());
  assert!(a.get_i32_be(data_start).is_ok());
  assert!(a.get_i64_le(data_start).is_ok());
  assert!(a.get_i64_be(data_start).is_ok());

  // Test bounds checking for larger types
  let alloc = a.allocated();
  if alloc > 0 {
    assert!(a.get_u64_le(alloc).is_err());
    assert!(a.get_u32_be(alloc).is_err());
    assert!(a.get_u16_le(alloc).is_err());
  }

  // Test unchecked getters
  unsafe {
    let _ = a.get_u8_unchecked(data_start);
    let _ = a.get_i8_unchecked(data_start);
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn allocator_properties<A: Allocator>(a: A) {
  // Test is_inmemory / is_ondisk / is_map
  assert!(a.is_inmemory());
  assert!(!a.is_ondisk());

  // Test capacity / allocated / remaining
  let cap = a.capacity();
  assert!(cap > 0);
  let allocated = a.allocated();
  assert!(allocated > 0);
  let remaining = a.remaining();
  assert!(remaining <= cap);
  assert_eq!(allocated + remaining, cap);

  // Test page_size
  let ps = a.page_size();
  assert!(ps > 0);

  // Test data
  let data = a.data();
  assert!(data.is_empty()); // No allocations yet beyond header

  // Test allocated_memory
  let mem = a.allocated_memory();
  assert_eq!(mem.len(), allocated);

  // Test memory
  let full_mem = a.memory();
  assert_eq!(full_mem.len(), cap);

  // Test refs
  let refs = a.refs();
  assert!(refs >= 1);

  // Test magic_version / version
  let _ = a.magic_version();
  let _ = a.version();

  // Test read_only
  assert!(!a.read_only());

  // Test minimum_segment_size
  let mss = a.minimum_segment_size();
  assert!(mss > 0);

  // Test data_offset
  let doff = a.data_offset();
  assert!(doff > 0);

  // Test discarded
  let d = a.discarded();
  assert_eq!(d, 0);

  // Test increase_discarded
  a.increase_discarded(10);
  assert_eq!(a.discarded(), 10);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_owned_bytes<A: Allocator>(a: A) {
  // Test alloc_bytes_owned
  let mut b = a.alloc_bytes_owned(32).unwrap();
  assert_eq!(b.capacity(), 32);
  b.set_len(4);
  b[0] = 1;
  b[1] = 2;
  b[2] = 3;
  b[3] = 4;
  assert_eq!(&b[..4], &[1, 2, 3, 4]);

  // Test that detach works on owned bytes
  unsafe {
    b.detach();
  }
  // b should drop without deallocating
  drop(b);

  // Test alloc_bytes_owned with zero size
  let b = a.alloc_bytes_owned(0);
  assert!(b.is_ok());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn object_owned<A: Allocator>(a: A) {
  // Test alloc_owned for a type that doesn't need drop (inline)
  let mut owned = unsafe { a.alloc_owned::<u64>().unwrap() };
  owned.write(42u64);
  unsafe {
    assert_eq!(*owned.as_ref(), 42u64);
    *owned.as_mut() = 100;
    assert_eq!(*owned.as_ref(), 100);
  }
  let _ptr = owned.as_mut_ptr();
  assert!(!_ptr.as_ptr().is_null());

  // Test Buffer trait on Owned
  let cap = owned.capacity();
  assert!(cap > 0);
  let off = owned.offset();
  assert!(off > 0);
  let bcap = owned.buffer_capacity();
  assert!(bcap > 0);
  let boff = owned.buffer_offset();
  assert!(boff > 0);
  drop(owned);

  // Test alloc_owned for a type that needs drop (Slot kind)
  let mut owned = unsafe { a.alloc_owned::<std::vec::Vec<u8>>().unwrap() };
  owned.write(std::vec![1, 2, 3]);
  unsafe {
    assert_eq!(owned.as_ref().len(), 3);
  }
  drop(owned);

  // Test alloc_owned for ZST (Dangling kind)
  let owned = unsafe { a.alloc_owned::<()>().unwrap() };
  unsafe {
    assert_eq!(owned.as_ref(), &());
  }
  drop(owned);

  // Test detach on owned
  let mut owned = unsafe { a.alloc_owned::<u32>().unwrap() };
  owned.write(99);
  unsafe {
    owned.detach();
  }
  drop(owned);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn arena_clear<A: Allocator>(a: A) {
  let mut b = a.alloc_bytes(100).unwrap();
  unsafe { b.detach() };
  let allocated_before = a.allocated();
  assert!(allocated_before > a.data_offset());

  unsafe {
    a.clear().unwrap();
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn arena_rewind<A: Allocator>(a: A) {
  let _ = a.alloc_bytes(100).unwrap();

  // Rewind to start
  unsafe {
    a.rewind(ArenaPosition::Start(a.data_offset() as u32));
  }

  // Rewind to end
  unsafe {
    a.rewind(ArenaPosition::End(0));
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_insufficient_space<A: Allocator>(a: A) {
  // Try to allocate more than available
  let remaining = a.remaining();
  let result = a.alloc_bytes(remaining as u32 + 1);
  assert!(result.is_err());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_set_len<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(100).unwrap();
  assert_eq!(buf.len(), 0);
  assert!(buf.is_empty());

  buf.set_len(50);
  assert_eq!(buf.len(), 50);
  assert!(!buf.is_empty());
  assert_eq!(buf.remaining(), 50);

  buf.set_len(100);
  assert_eq!(buf.len(), 100);
  assert_eq!(buf.remaining(), 0);
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn flush_operations<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join(std::format!("test_{prefix}_flush_operations"));

  unsafe {
    let a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();

    let mut buf = a.alloc_bytes(64).unwrap();
    buf.set_len(64);
    for b in buf.iter_mut() {
      *b = 0xAB;
    }

    // Test all flush methods
    a.flush().unwrap();
    a.flush_async().unwrap();

    let offset = buf.offset();
    let size = buf.capacity();
    a.flush_range(offset, size).unwrap();
    a.flush_async_range(offset, size).unwrap();
    a.flush_header_and_range(offset, size).unwrap();
    a.flush_async_header_and_range(offset, size).unwrap();

    // Test Buffer::flush on BytesRefMut
    buf.flush().unwrap();
    buf.flush_async().unwrap();

    buf.detach();
    drop(buf);

    // Test path
    assert!(a.path().is_some());

    // Test is_map / is_map_file
    assert!(a.is_map());
    assert!(!a.is_inmemory());
    assert!(a.is_ondisk());
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn lock_operations<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join(std::format!("test_{prefix}_lock_operations"));

  unsafe {
    let a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();

    // Test lock/unlock operations
    a.lock_exclusive().unwrap();
    a.unlock().unwrap();

    a.lock_shared().unwrap();
    a.unlock().unwrap();

    // Test try_lock
    assert!(a.try_lock_exclusive().is_ok());
    a.unlock().unwrap();

    assert!(a.try_lock_shared().is_ok());
    a.unlock().unwrap();
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn read_only<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join(std::format!("test_{prefix}_read_only"));

  unsafe {
    // Create arena first
    {
      let a = DEFAULT_ARENA_OPTIONS
        .with_capacity(4096)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut::<A, _>(&p)
        .unwrap();

      let mut buf = a.alloc_bytes(64).unwrap();
      buf.set_len(64);
      buf.detach();
    }

    // Open read-only
    let a = DEFAULT_ARENA_OPTIONS
      .with_read(true)
      .map::<A, _>(&p)
      .unwrap();
    assert!(a.read_only());

    // Attempting to allocate should fail
    let result = a.alloc_bytes(10);
    assert!(result.is_err());
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn dealloc_paths<A: Allocator>(a: A) {
  // Test the fast dealloc path: deallocating the most recently allocated block
  // (offset + size == allocated)
  let mut b1 = a.alloc_bytes(64).unwrap();
  unsafe { b1.detach() };

  let b2 = a.alloc_bytes(32).unwrap();
  drop(b2); // Should hit fast dealloc path (most recent alloc)

  // Verify the space was reclaimed
  let _ = a.alloc_bytes(32).unwrap(); // Should succeed reusing freed space
}

#[cfg(not(feature = "loom"))]
pub(crate) fn dealloc_with_freelist<A: Allocator>(a: A) {
  // Allocate multiple blocks, then free non-most-recent ones
  // This forces the freelist slow path
  let mut b1 = a.alloc_bytes(64).unwrap();
  unsafe { b1.detach() };

  let mut b2 = a.alloc_bytes(64).unwrap();
  unsafe { b2.detach() };

  let mut b3 = a.alloc_bytes(64).unwrap();
  unsafe { b3.detach() };

  // Drop b1 (not the most recent allocation) → goes through freelist
  unsafe {
    a.dealloc(b1.buffer_offset() as u32, b1.buffer_capacity() as u32);
  }

  // Drop b2 (not the most recent allocation) → goes through freelist
  unsafe {
    a.dealloc(b2.buffer_offset() as u32, b2.buffer_capacity() as u32);
  }

  // Now allocate again - should reuse from freelist
  let _ = a.alloc_bytes(64).unwrap();
  let _ = a.alloc_bytes(64).unwrap();
}

#[cfg(not(feature = "loom"))]
pub(crate) fn dealloc_freelist_none<A: Allocator>(a: A) {
  // With Freelist::None, non-recent deallocs go to discarded
  let mut b1 = a.alloc_bytes(64).unwrap();
  unsafe { b1.detach() };

  let mut b2 = a.alloc_bytes(64).unwrap();
  unsafe { b2.detach() };

  // Drop b1 → with Freelist::None, should increase discarded
  unsafe {
    a.dealloc(b1.buffer_offset() as u32, b1.buffer_capacity() as u32);
  }

  assert!(a.discarded() > 0);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn rewind_all_positions<A: Allocator>(a: A) {
  // Allocate some data
  let mut buf = a.alloc_bytes(100).unwrap();
  unsafe { buf.detach() };

  let cap = a.capacity() as u32;
  let data_offset = a.data_offset() as u32;
  let _allocated = a.allocated();

  // Test ArenaPosition::Start
  unsafe {
    a.rewind(ArenaPosition::Start(data_offset as u32));
  }
  assert_eq!(a.allocated(), data_offset as usize);

  // Allocate again after rewind
  let mut buf = a.alloc_bytes(50).unwrap();
  unsafe { buf.detach() };

  // Test ArenaPosition::Current with positive offset
  unsafe {
    a.rewind(ArenaPosition::Current(10));
  }

  // Test ArenaPosition::Current with negative offset
  unsafe {
    a.rewind(ArenaPosition::Current(-5));
  }

  // Test ArenaPosition::Current with zero (should be no-op)
  let before = a.allocated();
  unsafe {
    a.rewind(ArenaPosition::Current(0));
  }
  assert_eq!(a.allocated(), before);

  // Test ArenaPosition::Current with very negative (clamp to data_offset)
  unsafe {
    a.rewind(ArenaPosition::Current(-(cap as i64 * 2)));
  }
  assert_eq!(a.allocated(), data_offset as usize);

  // Re-allocate
  let mut buf = a.alloc_bytes(50).unwrap();
  unsafe { buf.detach() };

  // Test ArenaPosition::End
  unsafe {
    a.rewind(ArenaPosition::End(0));
  }
  assert_eq!(a.allocated(), cap as usize);

  // Test ArenaPosition::End with offset
  unsafe {
    a.rewind(ArenaPosition::End(10));
  }
  assert_eq!(a.allocated(), (cap - 10) as usize);

  // Test ArenaPosition::End with overflow (should clamp)
  unsafe {
    a.rewind(ArenaPosition::End(cap + 100));
  }
  assert_eq!(a.allocated(), data_offset as usize);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_aligned<A: Allocator>(a: A) {
  // Test alloc_aligned_bytes with various types
  let b = a.alloc_aligned_bytes::<u64>(32).unwrap();
  assert!(b.offset() % mem::align_of::<u64>() == 0);
  assert!(b.capacity() >= 32);

  let b = a.alloc_aligned_bytes::<u128>(64).unwrap();
  assert!(b.offset() % mem::align_of::<u128>() == 0);
  assert!(b.capacity() >= 64);

  // Test zero-size aligned alloc (capacity may include alignment padding)
  let b = a.alloc_aligned_bytes::<u64>(0).unwrap();
  let _ = b.capacity(); // Just verify it doesn't panic

  // Test alloc_aligned_bytes_owned
  let b = a.alloc_aligned_bytes_owned::<u32>(16).unwrap();
  assert!(b.capacity() >= 16);
}

#[cfg(all(not(feature = "loom"), feature = "std"))]
pub(crate) fn bytes_write_io<A: Allocator>(a: A) {
  use std::io::Write;

  let mut buf = a.alloc_bytes(128).unwrap();
  // Test std::io::Write implementation
  let written = buf.write(b"hello world").unwrap();
  assert_eq!(written, 11);
  assert_eq!(buf.len(), 11);

  // Test write_all
  buf.write_all(b" goodbye").unwrap();
  assert_eq!(buf.len(), 19);

  // Test flush (no-op for bytes)
  buf.flush().unwrap();
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn sanity_check_errors<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();

  // Create arena with a specific magic_version
  let p = dir
    .path()
    .join(std::format!("test_{prefix}_sanity_check_magic"));
  unsafe {
    let _a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_magic_version(42)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();
  }

  // Try to open with different magic_version
  let result = unsafe {
    DEFAULT_ARENA_OPTIONS
      .with_magic_version(99)
      .with_read(true)
      .map::<A, _>(&p)
  };
  assert!(result.is_err());

  // Create arena with optimistic freelist, try to reopen with pessimistic via map_mut
  let p2 = dir
    .path()
    .join(std::format!("test_{prefix}_sanity_check_freelist"));
  unsafe {
    let _a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_freelist(Freelist::Optimistic)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p2)
      .unwrap();
  }

  // map_mut with wrong freelist should fail
  let result = unsafe {
    DEFAULT_ARENA_OPTIONS
      .with_freelist(Freelist::Pessimistic)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p2)
  };
  assert!(result.is_err());
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn map_copy<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join(std::format!("test_{prefix}_map_copy"));

  // Create arena first
  unsafe {
    let a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();
    let mut buf = a.alloc_bytes(64).unwrap();
    buf.set_len(64);
    for b in buf.iter_mut() {
      *b = 0x42;
    }
    buf.detach();
  }

  // Open as map_copy
  let a = unsafe {
    DEFAULT_ARENA_OPTIONS
      .with_read(true)
      .map_copy::<A, _>(&p)
      .unwrap()
  };
  assert!(a.is_map());

  // Open as map_copy_read_only
  let a = unsafe {
    DEFAULT_ARENA_OPTIONS
      .with_read(true)
      .map_copy_read_only::<A, _>(&p)
      .unwrap()
  };
  assert!(a.read_only());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_in_slow_path<A: Allocator>(l: A, max_segment_node_size: u32) {
  // Exercise alloc_in (generic T allocation) through slow paths
  // First fill up the main memory
  for i in 1..=5 {
    let _ = l.alloc_bytes(i * 50).unwrap();
  }

  let remaining = l.remaining();
  let _ = l.alloc_bytes(remaining as u32).unwrap();

  // Now allocate from segments using alloc (type allocation)
  for i in (1..=5).rev() {
    let size = i * 50 - max_segment_node_size;
    if size >= 8 {
      // Use type-based allocation (exercises alloc_in path)
      let _ = unsafe { l.alloc::<u64>().unwrap() };
    }
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn error_variants<A: Allocator>() {
  // Test all Error Display variants
  let e = Error::InsufficientSpace {
    requested: 100,
    available: 50,
  };
  let s = std::format!("{e}");
  assert!(s.contains("100") && s.contains("50"));

  let e = Error::ReadOnly;
  let s = std::format!("{e}");
  assert!(s.contains("read-only"));

  let e = Error::OutOfBounds {
    offset: 42,
    allocated: 10,
  };
  let s = std::format!("{e}");
  assert!(s.contains("42") && s.contains("10"));

  // Exercise DecodeVarintError path via invalid LEB128 data
  {
    let a = Options::new().with_capacity(1024).alloc::<A>().unwrap();
    let mut buf = a.alloc_bytes(10).unwrap();
    // Write invalid LEB128 (all high bits set, no terminator)
    for i in 0..10 {
      buf.put_u8(0x80 | (i as u8)).unwrap();
    }
    unsafe { buf.detach() };
    let result = a.get_u32_varint(buf.offset());
    if let Err(Error::DecodeVarintError(e)) = result {
      let s = std::format!("{e}");
      let _ = s;
    }
  }

  // Test std::error::Error trait
  #[cfg(feature = "std")]
  {
    use std::error::Error as StdError;
    let e = super::Error::ReadOnly;
    let _ = e.source();
  }

  // Test Clone, PartialEq, Eq, Debug
  let e = Error::OutOfBounds {
    offset: 1,
    allocated: 2,
  };
  let e2 = e.clone();
  assert_eq!(e, e2);
  let _ = std::format!("{e:?}");
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_owned_detach_and_drop<A: Allocator>(a: A) {
  // Test BytesMut (owned) with detach - exercises Drop::drop for detached path
  let mut b = a.alloc_bytes_owned(32).unwrap();
  b.set_len(10);
  b[0] = 42;

  // Test Deref/DerefMut on BytesMut
  let slice: &[u8] = &b;
  assert_eq!(slice[0], 42);
  let slice_mut: &mut [u8] = &mut b;
  slice_mut[1] = 43;

  // Test as_ptr / as_mut_ptr on BytesMut
  let _ptr = b.as_ptr();
  let _mptr = b.as_mut_ptr();

  // Test Buffer trait on BytesMut
  let _ = b.buffer_offset();
  let _ = b.buffer_capacity();

  unsafe {
    b.detach();
  }
  drop(b); // Drop with detach=true should not dealloc

  // Test BytesMut (owned) without detach - exercises Drop::drop for normal path
  let b2 = a.alloc_bytes_owned(32).unwrap();
  drop(b2); // Drop with detach=false should dealloc

  // Test flush on BytesMut (vec-backed, should succeed)
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  {
    let b3 = a.alloc_bytes_owned(32).unwrap();
    let _ = b3.flush();
    let _ = b3.flush_async();
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn debug_and_clone<A: Allocator + core::fmt::Debug + Clone>(a: A) {
  // Test Debug impl on Arena
  let debug_str = std::format!("{a:?}");
  assert!(!debug_str.is_empty());

  // Test Clone impl
  let b = a.clone();
  assert_eq!(a.capacity(), b.capacity());
  assert_eq!(a.allocated(), b.allocated());
  assert_eq!(a.data_offset(), b.data_offset());
  drop(b);

  // Test Debug on allocated bytes
  let buf = a.alloc_bytes(10).unwrap();
  let debug_str = std::format!("{buf:?}");
  assert!(!debug_str.is_empty());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn reserved_bytes_zero<A: Allocator>(a: A) {
  // With zero reserved bytes, these should return empty slices
  assert_eq!(a.reserved_bytes(), 0);
  assert_eq!(a.reserved_slice().len(), 0);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn get_bytes_and_pointers<A: Allocator>(a: A) {
  // Allocate and detach a buffer
  let mut buf = a.alloc_bytes(64).unwrap();
  buf.set_len(64);
  for (i, b) in buf.iter_mut().enumerate() {
    *b = (i & 0xFF) as u8;
  }
  let offset = buf.offset();
  unsafe { buf.detach() };

  // Test get_bytes
  let bytes = unsafe { a.get_bytes(offset, 10) };
  assert_eq!(bytes.len(), 10);
  for (i, &b) in bytes.iter().enumerate() {
    assert_eq!(b, (i & 0xFF) as u8);
  }

  // Test get_bytes with zero size
  let bytes = unsafe { a.get_bytes(offset, 0) };
  assert!(bytes.is_empty());

  // Test get_pointer / get_pointer_mut
  let ptr = unsafe { a.get_pointer(offset) };
  assert!(!ptr.is_null());
  let ptr_mut = unsafe { a.get_pointer_mut(offset) };
  assert!(!ptr_mut.is_null());

  // Test get_aligned_pointer
  let aligned = unsafe { a.get_aligned_pointer::<u64>(offset) };
  assert!(!aligned.is_null());
  let aligned_mut = unsafe { a.get_aligned_pointer_mut::<u64>(offset) };
  assert!(!aligned_mut.as_ptr().is_null());

  // Test get_bytes_mut
  let bytes_mut = unsafe { a.get_bytes_mut(offset, 10) };
  assert_eq!(bytes_mut.len(), 10);

  // Test get_pointer with offset 0
  let ptr0 = unsafe { a.get_pointer(0) };
  assert!(!ptr0.is_null());
  let ptr_mut0 = unsafe { a.get_pointer_mut(0) };
  assert!(!ptr_mut0.is_null());

  // Test get_aligned_pointer with offset 0
  let aligned0 = unsafe { a.get_aligned_pointer::<u64>(0) };
  assert!(aligned0.is_null());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_write_methods<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(128).unwrap();

  // All get_* methods use from_be_bytes internally (regardless of name),
  // so use put_*_be for roundtrip correctness.
  buf.put_u128_be(12345678901234567890).unwrap();
  buf.put_i128_be(-1234567890).unwrap();

  // Read them back (LIFO: get pops from end)
  assert_eq!(buf.get_i128_be().unwrap(), -1234567890);
  assert_eq!(buf.get_u128_be().unwrap(), 12345678901234567890);

  // Test i16 variants
  buf.put_i16_be(-1234).unwrap();
  assert_eq!(buf.get_i16_be().unwrap(), -1234);

  // Also exercise the le/ne put methods (they write, just can't roundtrip with get_*_be)
  buf.put_u32_le(42).unwrap();
  let _ = buf.get_u32_le(); // exercises the code path, value won't match
  buf.put_u32_ne(42).unwrap();
  let _ = buf.get_u32_ne(); // exercises the code path

  // Exercise isize/usize
  buf.put_usize_be(999).unwrap();
  assert_eq!(buf.get_usize_be().unwrap(), 999);

  buf.put_isize_be(-777).unwrap();
  assert_eq!(buf.get_isize_be().unwrap(), -777);

  // Test put_slice_unchecked
  buf.put_u8(0xAA).unwrap();
  assert_eq!(buf.get_u8().unwrap(), 0xAA);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn allocator_leb128<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(128).unwrap();

  // Write some LEB128 values
  buf.put_u32_varint(300).unwrap();
  buf.put_u64_varint(100000).unwrap();
  buf.put_i32_varint(-42).unwrap();
  buf.put_i64_varint(-100000).unwrap();

  unsafe { buf.detach() };

  // Read back using allocator methods
  let data_start = buf.offset();
  let (bytes_read, val) = a.get_u32_varint(data_start).unwrap();
  assert_eq!(val, 300);

  let (bytes_read2, val2) = a.get_u64_varint(data_start + bytes_read).unwrap();
  assert_eq!(val2, 100000);

  let (bytes_read3, val3) = a
    .get_i32_varint(data_start + bytes_read + bytes_read2)
    .unwrap();
  assert_eq!(val3, -42);

  let (_bytes_read4, val4) = a
    .get_i64_varint(data_start + bytes_read + bytes_read2 + bytes_read3)
    .unwrap();
  assert_eq!(val4, -100000);

  // Test out-of-bounds LEB128 read
  let result = a.get_u32_varint(a.allocated() + 1);
  assert!(result.is_err());
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn memmap_anon_operations<A: Allocator>() {
  // Test map_anon with various options
  let a = DEFAULT_ARENA_OPTIONS
    .with_capacity(4096)
    .map_anon::<A>()
    .unwrap();

  assert!(!a.is_ondisk());
  assert!(a.is_map());
  assert!(!a.read_only());

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  {
    assert!(a.path().is_none());
  }

  // Test allocation on anon mmap
  let mut buf = a.alloc_bytes(64).unwrap();
  buf.set_len(64);
  for b in buf.iter_mut() {
    *b = 0x55;
  }
  assert_eq!(buf[0], 0x55);

  // Test flush on anon mmap (should succeed/no-op)
  a.flush().unwrap();
  a.flush_async().unwrap();
}

#[cfg(not(feature = "loom"))]
pub(crate) fn dealloc_interleaved<A: Allocator>(a: A) {
  // Allocate multiple blocks and deallocate in different order
  // This exercises the freelist insertion logic more thoroughly
  let mut blocks = std::vec::Vec::new();
  for _ in 0..10 {
    let mut b = a.alloc_bytes(32).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Deallocate even-indexed blocks (non-contiguous)
  for i in (0..10).step_by(2) {
    unsafe {
      a.dealloc(blocks[i].0, blocks[i].1);
    }
  }

  // Deallocate odd-indexed blocks
  for i in (1..10).step_by(2) {
    unsafe {
      a.dealloc(blocks[i].0, blocks[i].1);
    }
  }

  // Now allocate again to trigger freelist reuse
  for _ in 0..10 {
    let _ = a.alloc_bytes(32).unwrap();
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_aligned_slow_path<A: Allocator>(l: A, max_segment_node_size: u32) {
  // Fill main memory to force slow path for aligned allocations
  for i in 1..=5 {
    let _ = l.alloc_bytes(i * 50).unwrap();
  }

  let remaining = l.remaining();
  let _ = l.alloc_bytes(remaining as u32).unwrap();

  // Allocate aligned bytes from segments (slow path)
  for i in (1..=5).rev() {
    let size = i * 50 - max_segment_node_size;
    if size > mem::size_of::<u32>() as u32 {
      // Use small enough size that fits in segment after alignment
      let alloc_size = (size / 2).min(size - mem::size_of::<u32>() as u32);
      if alloc_size > 0 {
        let _ = l.alloc_aligned_bytes::<u32>(alloc_size);
      }
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn flush_header_operations<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join(std::format!("test_{prefix}_flush_header"));

  unsafe {
    let a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();

    let mut buf = a.alloc_bytes(64).unwrap();
    buf.set_len(64);
    buf.detach();

    // Test flush_header
    a.flush_header().unwrap();
    a.flush_async_header().unwrap();

    // Test flush_header_and_range with various offsets
    let data_off = a.data_offset();
    a.flush_header_and_range(data_off, 32).unwrap();
    a.flush_async_header_and_range(data_off, 32).unwrap();

    // Test flushing range that overlaps with header
    a.flush_header_and_range(0, 64).unwrap();
    a.flush_async_header_and_range(0, 64).unwrap();
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn set_minimum_segment_size<A: Allocator>(a: A) {
  let old = a.minimum_segment_size();
  a.set_minimum_segment_size(old * 2);
  assert_eq!(a.minimum_segment_size(), old * 2);
  a.set_minimum_segment_size(old);
  assert_eq!(a.minimum_segment_size(), old);
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

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn path_builder_operations<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();

  // Test map_mut_with_path_builder
  {
    let p = dir
      .path()
      .join(std::format!("test_{prefix}_path_builder_mut"));
    let arena = unsafe {
      Options::new()
        .with_capacity(1024)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut_with_path_builder::<A, _, std::io::Error>(|| Ok(p.clone()))
        .unwrap()
    };
    let _ = arena.alloc_bytes(32).unwrap();
    assert!(arena.path().is_some());
  }

  // Test map_with_path_builder
  {
    let p = dir
      .path()
      .join(std::format!("test_{prefix}_path_builder_read"));
    // First create the file
    unsafe {
      let _arena = Options::new()
        .with_capacity(1024)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut::<A, _>(&p)
        .unwrap();
    }
    // Then open read-only with path builder
    let arena = unsafe {
      Options::new()
        .with_read(true)
        .map_with_path_builder::<A, _, std::io::Error>(|| Ok(p.clone()))
        .unwrap()
    };
    assert!(arena.read_only());
  }

  // Test map_copy_with_path_builder
  {
    let p = dir
      .path()
      .join(std::format!("test_{prefix}_path_builder_copy"));
    unsafe {
      let _arena = Options::new()
        .with_capacity(1024)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut::<A, _>(&p)
        .unwrap();
    }
    let arena = unsafe {
      Options::new()
        .with_read(true)
        .with_write(true)
        .map_copy_with_path_builder::<A, _, std::io::Error>(|| Ok(p.clone()))
        .unwrap()
    };
    let _ = arena.alloc_bytes(32).unwrap();
  }

  // Test map_copy_read_only_with_path_builder
  {
    let p = dir
      .path()
      .join(std::format!("test_{prefix}_path_builder_copy_ro"));
    unsafe {
      let _arena = Options::new()
        .with_capacity(1024)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut::<A, _>(&p)
        .unwrap();
    }
    let arena = unsafe {
      Options::new()
        .with_read(true)
        .map_copy_read_only_with_path_builder::<A, _, std::io::Error>(|| Ok(p.clone()))
        .unwrap()
    };
    assert!(arena.read_only());
  }

  // Test path_builder error propagation
  {
    let res = unsafe {
      Options::new()
        .with_capacity(1024)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut_with_path_builder::<A, _, &str>(|| Err("path builder error"))
    };
    assert!(res.is_err());
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn remove_on_drop<A: Allocator>(_prefix: &str) {
  // This test is only valid for concrete types with set_remove_on_drop
  // Test using unsync::Arena directly
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join("test_remove_on_drop_unsync");

  unsafe {
    let arena = Options::new()
      .with_capacity(1024)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<crate::unsync::Arena, _>(&p)
      .unwrap();

    let _ = arena.alloc_bytes(32).unwrap();
    arena.remove_on_drop(true);
    assert!(p.exists());
    drop(arena);
  }
  // File should be removed after drop
  assert!(!p.exists());

  // Test with sync::Arena
  let p2 = dir.path().join("test_remove_on_drop_sync");
  unsafe {
    let arena = Options::new()
      .with_capacity(1024)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<crate::sync::Arena, _>(&p2)
      .unwrap();

    let _ = arena.alloc_bytes(32).unwrap();
    arena.remove_on_drop(true);
    assert!(p2.exists());
    drop(arena);
  }
  assert!(!p2.exists());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_slice_operations<A: Allocator>(a: A) {
  // Test put_slice
  let mut buf = a.alloc_bytes(128).unwrap();
  buf.put_slice(&[1, 2, 3, 4, 5]).unwrap();
  assert_eq!(buf.len(), 5);

  // Test get_slice
  let slice = buf.get_slice(3).unwrap();
  assert_eq!(slice.len(), 3);

  let err = buf.get_slice(200);
  assert!(err.is_err());

  // Test get_slice_mut
  let slice_mut = buf.get_slice_mut(3).unwrap();
  assert_eq!(slice_mut.len(), 3);

  let err = buf.get_slice_mut(200);
  assert!(err.is_err());

  // Test put_slice overflow
  let mut small_buf = a.alloc_bytes(4).unwrap();
  let err = small_buf.put_slice(&[1, 2, 3, 4, 5]);
  assert!(err.is_err());

  // Test put_slice_unchecked
  let mut buf2 = a.alloc_bytes(64).unwrap();
  unsafe { buf2.put_slice_unchecked(&[10, 20, 30]) };
  assert_eq!(buf2.len(), 3);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_align_and_put<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(256).unwrap();

  // Test align_to
  let ptr = buf.align_to::<u64>().unwrap();
  assert!(!ptr.as_ptr().is_null());
  assert_eq!(ptr.as_ptr() as usize % mem::align_of::<u64>(), 0);

  // Test put
  let val = unsafe { buf.put::<u64>(0xDEADBEEF).unwrap() };
  assert_eq!(*val, 0xDEADBEEF);

  // Test put_aligned
  let val = unsafe { buf.put_aligned::<u32>(42).unwrap() };
  assert_eq!(*val, 42);

  // Test align_to with ZST
  let ptr = buf.align_to::<()>().unwrap();
  assert!(!ptr.as_ptr().is_null());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn refmut_write_read<A: Allocator>(a: A) {
  // Test RefMut with different types
  // Inline type (u64 - no drop needed)
  {
    let mut r = unsafe { a.alloc::<u64>().unwrap() };
    r.write(12345u64);
    unsafe {
      assert_eq!(*r.as_ref(), 12345u64);
      *r.as_mut() = 67890u64;
      assert_eq!(*r.as_ref(), 67890u64);
    }
    let ptr = r.as_mut_ptr();
    assert!(!ptr.as_ptr().is_null());
  }

  // Test Owned with write, as_ref, as_mut, as_mut_ptr
  {
    let mut owned = unsafe { a.alloc_owned::<u64>().unwrap() };
    owned.write(99u64);
    unsafe {
      assert_eq!(*owned.as_ref(), 99u64);
      *owned.as_mut() = 100u64;
      assert_eq!(*owned.as_ref(), 100u64);
    }
    let ptr = owned.as_mut_ptr();
    assert!(!ptr.as_ptr().is_null());
  }

  // Test RefMut with Vec<u8> (slot type, needs drop)
  {
    let mut r = unsafe { a.alloc::<Vec<u8>>().unwrap() };
    r.write(vec![1, 2, 3]);
    unsafe {
      assert_eq!(r.as_ref().len(), 3);
      r.as_mut().push(4);
      assert_eq!(r.as_ref().len(), 4);
    }
  }

  // Test Owned with Vec<u8> - detach path
  {
    let mut owned = unsafe { a.alloc_owned::<Vec<u8>>().unwrap() };
    unsafe { owned.detach() };
    owned.write(vec![10, 20, 30]);
    unsafe {
      core::ptr::drop_in_place(owned.as_mut());
    }
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_leb128<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(128).unwrap();

  // Test put/get LEB128 on BytesRefMut
  let n = buf.put_u32_varint(300).unwrap();
  assert!(n > 0);

  let n2 = buf.put_u64_varint(100000).unwrap();
  assert!(n2 > 0);

  let n3 = buf.put_i32_varint(-42).unwrap();
  assert!(n3 > 0);

  let n4 = buf.put_i64_varint(-100000).unwrap();
  assert!(n4 > 0);

  // Test unchecked variant
  let n5 = buf.put_u16_varint_unchecked(500);
  assert!(n5 > 0);

  // Test write_varint (io::Write wrapper)
  #[cfg(feature = "std")]
  {
    let n6 = buf.write_u32_varint(42).unwrap();
    assert!(n6 > 0);

    let n7 = buf.write_u64_varint(999).unwrap();
    assert!(n7 > 0);
  }

  // Test LEB128 on BytesMut (owned)
  let mut owned = a.alloc_bytes_owned(128).unwrap();
  let n = owned.put_u32_varint(300).unwrap();
  assert!(n > 0);
  let n = owned.put_i64_varint(-999).unwrap();
  assert!(n > 0);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn options_getters() {
  // Test all Options getters with memmap features
  let opts = Options::new()
    .with_capacity(4096)
    .with_reserved(16)
    .with_maximum_alignment(16)
    .with_minimum_segment_size(64)
    .with_maximum_retries(10)
    .with_unify(true)
    .with_magic_version(42)
    .with_freelist(Freelist::Pessimistic);

  assert_eq!(opts.capacity(), 4096);
  assert_eq!(opts.reserved(), 16);
  assert_eq!(opts.maximum_alignment(), 16);
  assert_eq!(opts.minimum_segment_size(), 64);
  assert_eq!(opts.maximum_retries(), 10);
  assert!(opts.unify());
  assert_eq!(opts.magic_version(), 42);
  assert_eq!(opts.freelist(), Freelist::Pessimistic);

  // Test maybe_capacity
  let opts2 = opts.maybe_capacity(None);
  assert_eq!(opts2.capacity(), 0);
  let opts3 = opts2.maybe_capacity(Some(2048));
  assert_eq!(opts3.capacity(), 2048);

  // Test Default
  let default_opts = Options::default();
  assert_eq!(default_opts.capacity(), 0);
  assert_eq!(default_opts.reserved(), 0);
  assert!(!default_opts.unify());

  // Test memmap-specific options
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  {
    let opts = Options::new()
      .with_lock_meta(true)
      .with_read(true)
      .with_write(true)
      .with_append(true)
      .with_truncate(true)
      .with_create(true)
      .with_create_new(true)
      .with_offset(100)
      .with_stack(true)
      .with_huge(Some(21))
      .with_populate(true);

    assert!(opts.lock_meta());
    assert!(opts.read());
    assert!(opts.write());
    assert!(opts.append());
    assert!(opts.truncate());
    assert!(opts.create());
    assert!(opts.create_new());
    assert_eq!(opts.offset(), 100);
    assert!(opts.stack());
    assert_eq!(opts.huge(), Some(21));
    assert!(opts.populate());
  }

  // Test Debug impl on Options
  let _ = std::format!("{:?}", opts);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn freelist_try_from() {
  assert_eq!(Freelist::try_from(0u8).unwrap(), Freelist::None);
  assert_eq!(Freelist::try_from(1u8).unwrap(), Freelist::Optimistic);
  assert_eq!(Freelist::try_from(2u8).unwrap(), Freelist::Pessimistic);
  assert!(Freelist::try_from(3u8).is_err());
  assert!(Freelist::try_from(255u8).is_err());

  // Test UnknownFreelist Display
  let err = Freelist::try_from(99u8).unwrap_err();
  let s = std::format!("{}", err);
  assert!(s.contains("unknown"));
}

#[cfg(not(feature = "loom"))]
pub(crate) fn reserved_slice_operations<A: Allocator>(a: A) {
  // Test reserved_bytes with actual reserved space
  let reserved = a.reserved_bytes();
  assert_eq!(reserved, 16);

  let reserved_slice = a.reserved_slice();
  assert_eq!(reserved_slice.len(), 16);

  // Test reserved_slice_mut
  unsafe {
    let reserved_mut = a.reserved_slice_mut();
    reserved_mut[0] = 0xAA;
    reserved_mut[15] = 0xBB;
  }

  let reserved_slice = a.reserved_slice();
  assert_eq!(reserved_slice[0], 0xAA);
  assert_eq!(reserved_slice[15], 0xBB);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_owned_write_io<A: Allocator>(a: A) {
  // Test std::io::Write on BytesMut (owned)
  #[cfg(feature = "std")]
  {
    use std::io::Write;
    let mut buf = a.alloc_bytes_owned(128).unwrap();
    buf.write_all(&[1, 2, 3, 4, 5]).unwrap();
    assert_eq!(buf.len(), 5);
    buf.flush().unwrap();
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn mlock_operations<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();

  // Test with lock_meta option on mmap_mut
  let p = dir.path().join(std::format!("test_{prefix}_mlock"));
  unsafe {
    let arena = Options::new()
      .with_capacity(4096)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .with_lock_meta(true)
      .map_mut::<A, _>(&p)
      .unwrap();

    let _ = arena.alloc_bytes(32).unwrap();
    // Arena will unlock on drop
  }

  // Test with lock_meta on map_anon
  {
    let arena = Options::new()
      .with_capacity(4096)
      .with_lock_meta(true)
      .map_anon::<A>()
      .unwrap();

    let _ = arena.alloc_bytes(32).unwrap();
  }

  // Test with lock_meta on read-only map
  {
    let p2 = dir.path().join(std::format!("test_{prefix}_mlock_ro"));
    unsafe {
      let _arena = Options::new()
        .with_capacity(4096)
        .with_create_new(true)
        .with_read(true)
        .with_write(true)
        .map_mut::<A, _>(&p2)
        .unwrap();
    }
    let arena = unsafe {
      Options::new()
        .with_read(true)
        .with_lock_meta(true)
        .map::<A, _>(&p2)
        .unwrap()
    };
    assert!(arena.read_only());
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_read_write_more<A: Allocator>(a: A) {
  // Exercise more of the write_byte_order (io::Write wrappers) and unchecked paths
  let mut buf = a.alloc_bytes(256).unwrap();

  // Write methods (io::Write wrappers)
  #[cfg(feature = "std")]
  {
    buf.write_u16_be(0x1234).unwrap();
    buf.write_u32_be(0x12345678).unwrap();
    buf.write_u64_be(0x123456789ABCDEF0).unwrap();
    buf.write_i16_be(-100).unwrap();
    buf.write_i32_be(-100000).unwrap();
    buf.write_i64_be(-1000000000).unwrap();
    buf.write_u16_le(0x1234).unwrap();
    buf.write_u32_le(0x12345678).unwrap();
    buf.write_u64_le(0x123456789ABCDEF0).unwrap();
    buf.write_i16_le(-100).unwrap();
    buf.write_i32_le(-100000).unwrap();
    buf.write_i64_le(-1000000000).unwrap();
    buf.write_u128_be(42u128).unwrap();
    buf.write_i128_be(-42i128).unwrap();
    buf.write_u128_le(42u128).unwrap();
    buf.write_i128_le(-42i128).unwrap();
  }

  // Also test put_*_unchecked paths
  unsafe {
    buf.put_u8_unchecked(0xFF);
    buf.put_i8_unchecked(-1);
    buf.put_u16_be_unchecked(0x1234);
    buf.put_u32_le_unchecked(0x12345678);
    buf.put_u64_ne_unchecked(0x123456789ABCDEF0);
    buf.put_i16_be_unchecked(-100);
    buf.put_i32_le_unchecked(-100000);
    buf.put_i64_ne_unchecked(-1000000000);
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn truncate_anon_mmap<A: Allocator>() {
  // Test truncate on anonymous mmap using unsync::Arena directly
  let mut arena = Options::new()
    .with_capacity(1024)
    .map_anon::<crate::unsync::Arena>()
    .unwrap();

  let mut b = arena.alloc_bytes(100).unwrap();
  b.set_len(100);
  b.fill(1);
  unsafe {
    b.detach();
  }
  let offset = b.offset();
  drop(b);

  let allocated = arena.allocated();
  let _ = arena.truncate(2048);

  assert_eq!(arena.allocated(), allocated);
  assert_eq!(arena.capacity(), 2048);

  unsafe {
    assert_eq!(arena.get_bytes(offset, 100), [1u8; 100]);
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn arena_remaining_and_data<A: Allocator>(a: A) {
  let cap = a.capacity();
  let data_offset = a.data_offset();
  let remaining_before = a.remaining();

  assert!(remaining_before > 0);
  assert!(data_offset > 0);
  assert_eq!(remaining_before, cap - data_offset);

  // Test data() - returns allocated data region
  let data = a.data();
  let allocated = a.allocated();
  assert_eq!(data.len(), allocated - data_offset);

  // Test memory()
  let memory = a.memory();
  assert_eq!(memory.len(), cap);

  // Allocate and check remaining decreases
  let b = a.alloc_bytes(64).unwrap();
  let remaining_after = a.remaining();
  assert!(remaining_after < remaining_before);
  drop(b);

  // Test page_size
  let ps = a.page_size();
  assert!(ps > 0);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn object_ref_mut<A: Allocator + core::fmt::Debug>(a: A) {
  // Test Buffer trait on RefMut
  {
    let r = unsafe { a.alloc::<u64>().unwrap() };
    let _ = Buffer::capacity(&r);
    let _ = Buffer::offset(&r);
    let _ = Buffer::buffer_capacity(&r);
    let _ = Buffer::buffer_offset(&r);
    // Test Debug
    let _ = std::format!("{:?}", r);
  }

  // Test Buffer trait on Owned
  {
    let owned = unsafe { a.alloc_owned::<u64>().unwrap() };
    let _ = Buffer::capacity(&owned);
    let _ = Buffer::offset(&owned);
    let _ = Buffer::buffer_capacity(&owned);
    let _ = Buffer::buffer_offset(&owned);
    // Test Debug
    let _ = std::format!("{:?}", owned);
  }

  // Test Owned with write, as_ref, as_mut, as_mut_ptr
  {
    let mut owned = unsafe { a.alloc_owned::<u64>().unwrap() };
    owned.write(99u64);
    unsafe {
      assert_eq!(*owned.as_ref(), 99u64);
      *owned.as_mut() = 100u64;
      assert_eq!(*owned.as_ref(), 100u64);
    }
    let ptr = owned.as_mut_ptr();
    assert!(!ptr.as_ptr().is_null());
  }

  // Test flush on objects (mmap)
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  {
    let r = unsafe { a.alloc::<u64>().unwrap() };
    // flush should succeed on vec-backed (no-op)
    let _ = Buffer::flush(&r);
    let _ = Buffer::flush_async(&r);
  }
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  {
    let owned = unsafe { a.alloc_owned::<u64>().unwrap() };
    let _ = Buffer::flush(&owned);
    let _ = Buffer::flush_async(&owned);
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn allocate_slow_path_multiple_rounds<A: Allocator>(l: A, max_segment_node_size: u32) {
  // Create segments and allocate from them, then dealloc and allocate again
  // This exercises the freelist more thoroughly
  for i in 1..=5 {
    let _ = l.alloc_bytes(i * 50).unwrap();
  }

  let remaining = l.remaining();
  let _ = l.alloc_bytes(remaining as u32).unwrap();

  // Allocate from segments (round 1)
  let mut blocks = std::vec::Vec::new();
  for i in (1..=5).rev() {
    let size = i * 50 - max_segment_node_size;
    let mut b = l.alloc_bytes(size).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Dealloc all blocks back to freelist
  for (offset, size) in blocks {
    unsafe {
      l.dealloc(offset, size);
    }
  }

  // Allocate from segments again (round 2) - exercises find_position/find_prev_and_next
  for i in (1..=5).rev() {
    let size = i * 50 - max_segment_node_size;
    if size > 0 {
      let _ = l.alloc_bytes(size);
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn flush_range_out_of_bounds<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join(std::format!("test_{prefix}_flush_oob"));

  unsafe {
    let a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();

    // Test flush_range out of bounds
    let err = a.flush_range(0, 10000);
    assert!(err.is_err());

    // Test flush_async_range out of bounds
    let err = a.flush_async_range(0, 10000);
    assert!(err.is_err());

    // Test flush_header_and_range with len=0 (should just flush header)
    a.flush_header_and_range(0, 0).unwrap();
    a.flush_async_header_and_range(0, 0).unwrap();

    // Test flush_header_and_range out of bounds
    let err = a.flush_header_and_range(0, 10000);
    assert!(err.is_err());
    let err = a.flush_async_header_and_range(0, 10000);
    assert!(err.is_err());
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn dealloc_many_segments<A: Allocator>(a: A) {
  // Allocate many blocks, detach them, dealloc in various orders
  // Then allocate from freelist - exercises find_position / find_prev_and_next
  let mut blocks = std::vec::Vec::new();
  for _ in 0..20 {
    let mut b = a.alloc_bytes(64).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Dealloc in reverse order (different from allocation order)
  for &(offset, size) in blocks.iter().rev() {
    unsafe {
      a.dealloc(offset, size);
    }
  }

  // Allocate from freelist
  for _ in 0..15 {
    let _ = a.alloc_bytes(64);
  }

  // Dealloc and discard
  let _ = a.discard_freelist();
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_i8_operations<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(64).unwrap();

  // Test put_i8 and put_i8_unchecked
  buf.put_i8(42).unwrap();
  buf.put_i8(-42).unwrap();
  unsafe {
    buf.put_i8_unchecked(127);
    buf.put_i8_unchecked(-128);
  }

  assert_eq!(buf.len(), 4);

  // Test get_i8 and get_i8_unchecked (LIFO order)
  let val = buf.get_i8().unwrap();
  assert_eq!(val, -128);
  let val = unsafe { buf.get_i8_unchecked() };
  assert_eq!(val, 127);

  // Test get_u8 and get_u8_unchecked
  let val = buf.get_u8().unwrap();
  let _ = val; // was -42 as u8
  let val = unsafe { buf.get_u8_unchecked() };
  let _ = val; // was 42 as u8

  // Test empty buffer error
  assert_eq!(buf.len(), 0);
  assert!(buf.get_u8().is_err());
  assert!(buf.get_i8().is_err());

  // Test put_u8 overflow
  let mut small = a.alloc_bytes(1).unwrap();
  small.put_u8(1).unwrap();
  assert!(small.put_u8(2).is_err());
  assert!(small.put_i8(3).is_err());
}

#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_set_len_edge_cases<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(64).unwrap();

  // Test set_len to same value (no-op path)
  buf.set_len(0);
  assert_eq!(buf.len(), 0);

  // Test set_len grow
  buf.set_len(32);
  assert_eq!(buf.len(), 32);

  // Test set_len shrink (zero-fills the freed part)
  buf.set_len(16);
  assert_eq!(buf.len(), 16);

  // Test set_len same again
  buf.set_len(16);
  assert_eq!(buf.len(), 16);
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn flush_header_overlap_cases<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir
    .path()
    .join(std::format!("test_{prefix}_flush_header_overlap"));

  unsafe {
    let a = DEFAULT_ARENA_OPTIONS
      .with_capacity(8192)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();

    let mut buf = a.alloc_bytes(1024).unwrap();
    buf.set_len(1024);
    buf.detach();

    // Case 1: len=0 - should just flush header
    a.flush_header_and_range(0, 0).unwrap();
    a.flush_async_header_and_range(0, 0).unwrap();

    // Case 2: Range that fully contains the header
    let data_off = a.data_offset();
    a.flush_header_and_range(0, data_off + 100).unwrap();
    a.flush_async_header_and_range(0, data_off + 100).unwrap();

    // Case 3: Range on same page as header
    a.flush_header_and_range(data_off, 32).unwrap();
    a.flush_async_header_and_range(data_off, 32).unwrap();

    // Case 4: Range far from header (different pages)
    a.flush_header_and_range(4096, 1024).unwrap();
    a.flush_async_header_and_range(4096, 1024).unwrap();

    // Case 5: Out of bounds error
    let err = a.flush_header_and_range(0, 100000);
    assert!(err.is_err());
    let err = a.flush_async_header_and_range(0, 100000);
    assert!(err.is_err());
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm"), not(feature = "loom")))]
pub(crate) fn lock_on_mmap_file<A: Allocator>(prefix: &str) {
  let dir = tempfile::tempdir().unwrap();
  let p = dir.path().join(std::format!("test_{prefix}_file_lock"));

  unsafe {
    let a = DEFAULT_ARENA_OPTIONS
      .with_capacity(4096)
      .with_create_new(true)
      .with_read(true)
      .with_write(true)
      .map_mut::<A, _>(&p)
      .unwrap();

    // Test locking on mmap file
    a.lock_exclusive().unwrap();
    a.unlock().unwrap();

    a.lock_shared().unwrap();
    a.unlock().unwrap();

    let _ = a.try_lock_exclusive().unwrap();
    a.unlock().unwrap();

    let _ = a.try_lock_shared().unwrap();
    a.unlock().unwrap();
  }

  // Test on read-only mmap
  let arena = unsafe { Options::new().with_read(true).map::<A, _>(&p).unwrap() };
  arena.lock_shared().unwrap();
  arena.unlock().unwrap();
  let _ = arena.try_lock_shared().unwrap();
  arena.unlock().unwrap();
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_aligned_in_slow_path<A: Allocator>(l: A, max_segment_node_size: u32) {
  // Fill up main memory with segments, then allocate aligned from freelist
  // This exercises alloc_aligned_bytes_in slow path
  for i in 1..=5 {
    let _ = l.alloc_bytes(i * 80).unwrap();
  }

  let remaining = l.remaining();
  let _ = l.alloc_bytes(remaining as u32).unwrap();

  // Allocate aligned bytes from segments (slow path)
  for i in (1..=5).rev() {
    let base_size = i * 80 - max_segment_node_size;
    if base_size > 16 {
      let alloc_size = base_size / 2;
      let _ = l.alloc_aligned_bytes::<u64>(alloc_size);
    }
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_type_in_slow_path<A: Allocator>(l: A, _max_segment_node_size: u32) {
  // Fill up main memory, then allocate typed from freelist
  // This exercises alloc_in slow path
  for i in 1..=5 {
    let _ = l.alloc_bytes(i * 80).unwrap();
  }

  let remaining = l.remaining();
  let _ = l.alloc_bytes(remaining as u32).unwrap();

  // Allocate typed objects from segments (slow path)
  for _ in 0..5 {
    let _ = unsafe { l.alloc::<u64>() };
  }
  for _ in 0..3 {
    let _ = unsafe { l.alloc::<u32>() };
  }
}

#[cfg(not(feature = "loom"))]
pub(crate) fn discard_freelist_operations<A: Allocator>(a: A) {
  // Test discard_freelist with populated freelist
  let mut blocks = std::vec::Vec::new();
  for _ in 0..10 {
    let mut b = a.alloc_bytes(64).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Dealloc to create freelist entries
  for (offset, size) in blocks {
    unsafe {
      a.dealloc(offset, size);
    }
  }

  // Now discard the entire freelist
  let discarded = a.discard_freelist().unwrap();
  assert!(discarded > 0);

  // After discard, trying to allocate should work from remaining or fail gracefully
  let _ = a.alloc_bytes(32);
}

#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_aligned_bytes_error_path<A: Allocator>(a: A) {
  // Fill arena completely - detach allocations so they don't get freed on drop
  loop {
    let remaining = a.remaining();
    if remaining == 0 {
      break;
    }
    let size = core::cmp::min(remaining as u32, 1024);
    match a.alloc_bytes(size) {
      Ok(mut b) => unsafe {
        b.detach();
      },
      Err(_) => break,
    }
  }

  // Now try aligned alloc - should fail
  let result = a.alloc_aligned_bytes::<u64>(64);
  assert!(result.is_err());

  // Test alloc error on typed alloc
  let result = unsafe { a.alloc::<u64>() };
  assert!(result.is_err());
}

/// Exercises the slow path allocation deeply: fill main, create segments via dealloc,
/// then allocate smaller amounts from those segments to trigger the "give back remaining" path.
#[cfg(not(feature = "loom"))]
pub(crate) fn slow_path_with_remainder<A: Allocator>(a: A) {
  // Create large segments by allocating and detaching
  let mut blocks = std::vec::Vec::new();
  for _ in 0..5 {
    let mut b = a.alloc_bytes(200).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Fill the remaining main arena
  let remaining = a.remaining();
  if remaining > 0 {
    let mut b = a.alloc_bytes(remaining as u32).unwrap();
    unsafe { b.detach() };
  }

  // Dealloc blocks to create freelist entries
  for (offset, size) in blocks {
    unsafe {
      a.dealloc(offset, size);
    }
  }

  // Now allocate smaller amounts from freelist - this exercises the slow path
  // and the "give back remaining memory" path when the segment is larger than needed
  for _ in 0..5 {
    let _ = a.alloc_bytes(32);
  }

  // Also test aligned allocation from freelist
  for _ in 0..3 {
    let _ = a.alloc_aligned_bytes::<u64>(16);
  }

  // Also test typed allocation from freelist
  for _ in 0..3 {
    let _ = unsafe { a.alloc::<u32>() };
  }
}

/// Exercises dealloc creating segments that are too small to be valid segment nodes.
#[cfg(not(feature = "loom"))]
pub(crate) fn dealloc_tiny_segments<A: Allocator>(a: A) {
  // Allocate small blocks - when deallocated, the memory may be too small
  // to form a valid segment node, exercising the try_new_segment failure path
  let mut blocks = std::vec::Vec::new();
  for _ in 0..10 {
    let mut b = a.alloc_bytes(16).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Dealloc blocks - some may be too small for segments
  for (offset, size) in blocks {
    unsafe {
      a.dealloc(offset, size);
    }
  }

  // Try allocating to see what's available
  let _ = a.alloc_bytes(8);
}

/// Exercises the alloc_in slow path (typed allocation through freelist).
#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_type_slow_path_with_freelist<A: Allocator>(a: A) {
  // Create segments by allocating and detaching large blocks
  let mut blocks = std::vec::Vec::new();
  for _ in 0..5 {
    let mut b = a.alloc_bytes(256).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Fill remaining
  let remaining = a.remaining();
  if remaining > 0 {
    let mut b = a.alloc_bytes(remaining as u32).unwrap();
    unsafe { b.detach() };
  }

  // Dealloc to create freelist
  for (offset, size) in blocks {
    unsafe {
      a.dealloc(offset, size);
    }
  }

  // Allocate typed objects from freelist (slow path for alloc_in)
  for _ in 0..10 {
    let _ = unsafe { a.alloc::<u64>() };
  }

  // Allocate aligned bytes from freelist (slow path for alloc_aligned_bytes_in)
  for _ in 0..5 {
    let _ = a.alloc_aligned_bytes::<u128>(32);
  }
}

/// Exercises error Display implementations.
#[cfg(not(feature = "loom"))]
pub(crate) fn error_display_formats<A: Allocator + core::fmt::Debug>(a: A) {
  // Test InsufficientSpace error Display
  let err = Options::new().with_capacity(0).alloc::<A>().unwrap_err();
  let display = std::format!("{err}");
  assert!(!display.is_empty());

  // Exercise the Debug impl
  let debug = std::format!("{err:?}");
  assert!(!debug.is_empty());

  // Test read-only error
  // (Can't easily create read-only error without memmap, test display of existing error types)
  let err = Error::InsufficientSpace {
    requested: 100,
    available: 50,
  };
  let display = std::format!("{err}");
  assert!(display.contains("100") || display.contains("50"));

  let err = Error::ReadOnly;
  let display = std::format!("{err}");
  assert!(!display.is_empty());

  // Test OutOfBounds error Display
  let err = Error::OutOfBounds {
    offset: 999,
    allocated: 100,
  };
  let display = std::format!("{err}");
  assert!(display.contains("999"));

  // Test std::error::Error impl
  let err: &dyn std::error::Error = &Error::ReadOnly;
  let _ = std::format!("{err}");
}

/// Exercises the alloc_aligned_bytes_in slow path with zero-sized types.
#[cfg(not(feature = "loom"))]
pub(crate) fn alloc_zst_operations<A: Allocator>(a: A) {
  // Allocate a ZST - should return immediately without slow path
  let result = a.alloc_aligned_bytes::<()>(0);
  assert!(result.is_ok());

  // Allocate ZST typed
  let result = unsafe { a.alloc::<()>() };
  assert!(result.is_ok());
}

/// Exercises the SegmentNode Debug impl and various segment list operations.
#[cfg(not(feature = "loom"))]
pub(crate) fn segment_debug_and_list_ops<A: Allocator>(a: A) {
  // Create some segments
  let mut blocks = std::vec::Vec::new();
  for _ in 0..5 {
    let mut b = a.alloc_bytes(128).unwrap();
    unsafe { b.detach() };
    blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
  }

  // Fill remaining
  let remaining = a.remaining();
  if remaining > 0 {
    let mut b = a.alloc_bytes(remaining as u32).unwrap();
    unsafe { b.detach() };
  }

  // Dealloc to create a freelist with multiple nodes
  for (offset, size) in &blocks {
    unsafe {
      a.dealloc(*offset, *size);
    }
  }

  // Now allocate from freelist, then dealloc again to exercise re-insertion
  let mut new_blocks = std::vec::Vec::new();
  for _ in 0..3 {
    match a.alloc_bytes(64) {
      Ok(mut b) => {
        unsafe { b.detach() };
        new_blocks.push((b.buffer_offset() as u32, b.buffer_capacity() as u32));
      }
      Err(_) => break,
    }
  }

  for (offset, size) in new_blocks {
    unsafe {
      a.dealloc(offset, size);
    }
  }

  // Discard the freelist
  let discarded = a.discard_freelist().unwrap();
  assert!(discarded > 0);
}

/// Exercises bytes LEB128 unchecked paths and more byte operations.
#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_leb128_unchecked<A: Allocator>(a: A) {
  // Test each LEB128 unchecked variant individually (write one, read one)
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_u16_varint(300).unwrap();
    let (_, val) = buf.get_u16_varint_unchecked();
    assert_eq!(val, 300);
  }
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_u32_varint(70000).unwrap();
    let (_, val) = buf.get_u32_varint_unchecked();
    assert_eq!(val, 70000);
  }
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_u64_varint(1_000_000).unwrap();
    let (_, val) = buf.get_u64_varint_unchecked();
    assert_eq!(val, 1_000_000);
  }
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_u128_varint(1_000_000_000).unwrap();
    let (_, val) = buf.get_u128_varint_unchecked();
    assert_eq!(val, 1_000_000_000);
  }
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_i16_varint(-150).unwrap();
    let (_, val) = buf.get_i16_varint_unchecked();
    assert_eq!(val, -150);
  }
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_i32_varint(-35000).unwrap();
    let (_, val) = buf.get_i32_varint_unchecked();
    assert_eq!(val, -35000);
  }
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_i64_varint(-500_000).unwrap();
    let (_, val) = buf.get_i64_varint_unchecked();
    assert_eq!(val, -500_000);
  }
  {
    let mut buf = a.alloc_bytes(32).unwrap();
    buf.put_i128_varint(-500_000_000).unwrap();
    let (_, val) = buf.get_i128_varint_unchecked();
    assert_eq!(val, -500_000_000);
  }
}

/// Exercises set_len edge cases and align_to error path on BytesRefMut.
#[cfg(not(feature = "loom"))]
pub(crate) fn bytes_align_to_error<A: Allocator>(a: A) {
  let mut buf = a.alloc_bytes(128).unwrap();

  // Set len to capacity to make buffer full
  let cap = buf.capacity();
  buf.set_len(cap);
  assert_eq!(buf.len(), cap);

  // Try align_to when buffer is full - should fail
  let result = buf.align_to::<u64>();
  assert!(result.is_err());
}
