use core::ptr::NonNull;

use super::*;

macro_rules! impl_bytes_utils_for_allocator {
  ($this:ident::$from:ident($ty:ident, $offset:ident)) => {{
    const SIZE: usize = core::mem::size_of::<$ty>();

    let allocated = $this.allocated();
    if $offset + SIZE > allocated {
      return Err(Error::OutOfBounds { $offset, allocated });
    }

    let buf = unsafe {
      let ptr = $this.raw_ptr().add($offset);
      core::slice::from_raw_parts(ptr, SIZE)
    };

    Ok($ty::$from(buf.try_into().unwrap()))
  }};
  (unsafe $this:ident::$from:ident($ty:ident, $offset:ident)) => {{
    const SIZE: usize = core::mem::size_of::<$ty>();

    let buf = unsafe {
      let ptr = $this.raw_ptr().add($offset);
      core::slice::from_raw_parts(ptr, SIZE)
    };

    $ty::$from(buf.try_into().unwrap())
  }};
}

macro_rules! define_bytes_utils {
  ($($ty:ident:$endian:literal), +$(,)?) => {
    $(
      paste::paste! {
        #[doc = "Returns a `" $ty "` from the allocator."]
        fn [< get_ $ty _ $endian >](&self, offset: usize) -> Result<$ty, Error> {
          impl_bytes_utils_for_allocator!(self::[< from_ $endian _bytes >]($ty, offset))
        }

        #[doc = "Returns a `" $ty "` from the allocator without bounds checking."]
        ///
        /// ## Safety
        /// - `offset..offset + size` must be within allocated memory.
        unsafe fn [< get_ $ty _ $endian _unchecked>](&self, offset: usize) -> $ty {
          impl_bytes_utils_for_allocator!(unsafe self::[< from_ $endian _bytes >]($ty, offset))
        }
      }
    )*
  };
}

macro_rules! impl_leb128_utils_for_allocator {
  ($this:ident($ty:ident, $offset:ident, $size:literal)) => {{
    let allocated = $this.allocated();
    if $offset >= allocated {
      return Err(Error::OutOfBounds { $offset, allocated });
    }

    let buf = unsafe {
      let ptr = $this.get_pointer($offset);
      let gap = (allocated - $offset).min($size);
      core::slice::from_raw_parts(ptr, gap)
    };

    paste::paste! {
      dbutils::leb128::[< decode_ $ty _varint >](buf).map_err(Into::into)
    }
  }};
}

macro_rules! define_leb128_utils {
  ($($ty:ident:$size:literal), +$(,)?) => {
    $(
      paste::paste! {
        #[doc = "Returns a `" $ty "` in LEB128 format from the allocator at the given offset."]
        ///
        /// ## Safety
        /// - `offset` must be within the allocated memory of the allocator.
        fn [< get_ $ty _varint >](&self, offset: usize) -> Result<(usize, $ty), Error> {
          impl_leb128_utils_for_allocator!(self($ty, offset, $size))
        }
      }
    )*
  };
}

/// A trait for easily interacting with the sync and unsync allocator allocators.
pub trait Allocator: sealed::Sealed {
  /// The path type of the allocator.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  type Path;

  /// Returns the number of bytes that are reserved by the allocator.
  fn reserved_bytes(&self) -> usize;

  /// Returns the reserved bytes of the allocator specified in the [`Options::with_reserved`].
  fn reserved_slice(&self) -> &[u8];

  /// Returns the mutable reserved bytes of the allocator specified in the [`Options::with_reserved`].
  ///
  /// ## Safety
  /// - The caller need to make sure there is no data-race
  ///
  /// # Panic
  /// - If in read-only mode, and num of reserved bytes is greater than 0, this method will panic.
  #[allow(clippy::mut_from_ref)]
  unsafe fn reserved_slice_mut(&self) -> &mut [u8];

  /// Allocates a `T` in the allocator.
  ///
  /// ## Safety
  ///
  /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`](crate::RefMut::detach),
  ///   then the caller must ensure that the `T` is dropped before the allocator is dropped.
  ///   Otherwise, it will lead to memory leaks.
  ///
  /// - If this is file backed allocator, then `T` must be recoverable from bytes.
  ///   1. Types require allocation are not recoverable.
  ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
  ///      although those types are on stack, but they cannot be recovered, when reopens the file.
  ///
  /// ## Examples
  ///
  /// ## Memory leak
  ///
  /// The following example demonstrates the memory leak when the `T` is a heap allocated type and detached.
  ///
  /// ```ignore
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  ///
  /// {
  ///   let mut data = arena.alloc::<Vec<u8>>().unwrap();
  ///   data.detach();
  ///   data.write(vec![1, 2, 3]);
  /// }
  ///
  /// drop(arena); // memory leak, the `Vec<u8>` is not dropped.
  /// ```
  ///
  /// ## Undefined behavior
  ///
  /// The following example demonstrates the undefined behavior when the `T` is not recoverable.
  ///
  /// ```ignore
  ///
  /// struct TypeOnHeap {
  ///   data: Vec<u8>,
  /// }
  ///
  /// let arena = Options::new().with_create_new(1000).with_read(true).with_write(true).map_mut::<Arena, _>("path/to/file").unwrap();
  ///
  /// let mut data = arena.alloc::<TypeOnHeap>().unwrap();
  /// data.detach();
  /// data.write(TypeOnHeap { data: vec![1, 2, 3] });
  /// let offset = data.offset();
  /// drop(arena);
  ///
  /// // reopen the file
  /// let arena = Options::new().with_read(true).map::<Arena, _>("path/to/file").unwrap();
  ///
  /// let foo = &*arena.get_aligned_pointer::<TypeOnHeap>(offset as usize);
  /// let b = foo.data[1]; // undefined behavior, the `data`'s pointer stored in the file is not valid anymore.
  /// ```
  ///
  /// ## Good practice
  ///
  /// Some examples about how to use this method correctly.
  ///
  /// ### Heap allocated type with carefull memory management
  ///
  /// ```ignore
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  ///
  /// // Do not invoke detach, so when the data is dropped, the drop logic will be handled by the allocator.
  /// // automatically.
  /// {
  ///   let mut data = arena.alloc::<Vec<u8>>().unwrap();
  ///   data.write(vec![1, 2, 3]);
  /// }
  ///
  ///
  /// let mut detached_data = arena.alloc::<Vec<u8>>().unwrap();
  /// detached_data.detach();
  /// detached_data.write(vec![4, 5, 6]);
  ///
  /// // some other logic
  ///
  /// core::ptr::drop_in_place(detached_data.as_mut()); // drop the `Vec` manually.
  ///
  /// drop(arena); // it is safe, the `Vec` is already dropped.
  /// ```
  ///
  /// ### Recoverable type with file backed allocator
  ///
  /// ```ignore
  ///
  /// struct Recoverable {
  ///   field1: u64,
  ///   field2: AtomicU32,
  /// }
  ///
  /// let arena = Options::new().with_create_new(1000).with_read(true).with_write(true).map_mut::<Arena, _>("path/to/file").unwrap();
  ///
  /// let mut data = arena.alloc::<Recoverable>().unwrap();
  /// data.write(Recoverable { field1: 10, field2: AtomicU32::new(20) });
  /// data.detach();
  /// let offset = data.offset();
  /// drop(arena);
  ///
  /// // reopen the file
  /// let arena = Options::new().with_read(true).map::<Arena, _>("path/to/file").unwrap();
  ///
  /// let foo = &*arena.get_aligned_pointer::<Recoverable>(offset as usize);
  ///
  /// assert_eq!(foo.field1, 10);
  /// assert_eq!(foo.field2.load(Ordering::Acquire), 20);
  /// ```
  unsafe fn alloc<T>(&self) -> Result<RefMut<'_, T, Self>, Error>;

  /// Allocates a byte slice that can hold a well-aligned `T` and extra `size` bytes.
  ///
  /// The layout of the allocated memory is:
  ///
  /// ```text
  /// | T | [u8; size] |
  /// ```
  ///
  /// ## Example
  ///
  /// ```ignore
  /// let mut bytes = arena.alloc_aligned_bytes::<T>(extra).unwrap();
  /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  /// ```
  fn alloc_aligned_bytes<T>(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error>;

  /// Allocates an owned byte slice that can hold a well-aligned `T` and extra `size` bytes.
  ///
  /// The layout of the allocated memory is:
  ///
  /// ```text
  /// | T | [u8; size] |
  /// ```
  ///
  /// ## Example
  ///
  /// ```ignore
  /// let mut bytes = arena.alloc_aligned_bytes_owned::<T>(extra).unwrap();
  /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  /// ```
  fn alloc_aligned_bytes_owned<T>(&self, size: u32) -> Result<BytesMut<Self>, Error> {
    self
      .alloc_aligned_bytes::<T>(size)
      .map(|mut b| b.to_owned())
  }

  // /// Allocates an owned byte slice that can hold a well-aligned `T` and extra `size` bytes.
  // ///
  // /// The layout of the allocated memory is:
  // ///
  // /// ```text
  // /// | T | [u8; size] |
  // /// ```
  // ///
  // /// ## Example
  // ///
  // /// ```ignore
  // /// let mut bytes = arena.alloc_aligned_bytes_owned_within_page::<T>(extra).unwrap();
  // /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  // /// ```
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // fn alloc_aligned_bytes_owned_within_page<T>(&self, size: u32) -> Result<BytesMut<Self>, Error> {
  //   self
  //     .alloc_aligned_bytes_within_page::<T>(size)
  //     .map(|mut b| b.to_owned())
  // }

  // /// Allocates a byte slice that can hold a well-aligned `T` and extra `size` bytes within a page.
  // ///
  // /// The layout of the allocated memory is:
  // ///
  // /// ```text
  // /// | T | [u8; size] |
  // /// ```
  // ///
  // /// ## Example
  // ///
  // /// ```ignore
  // /// let mut bytes = arena.alloc_aligned_bytes_within_page::<T>(extra).unwrap();
  // /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  // /// ```
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // fn alloc_aligned_bytes_within_page<T>(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error>;

  /// Allocates a slice of memory in the allocator.
  ///
  /// The [`BytesRefMut`](crate::BytesRefMut) is zeroed out.
  ///
  /// If you want a [`BytesMut`](crate::BytesMut), see [`alloc_bytes_owned`](Allocator::alloc_bytes_owned).
  fn alloc_bytes(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error>;

  /// Allocates an owned slice of memory in the allocator.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes`](Allocator::alloc_bytes).
  fn alloc_bytes_owned(&self, size: u32) -> Result<BytesMut<Self>, Error> {
    self.alloc_bytes(size).map(|mut b| b.to_owned())
  }

  // /// Allocates an owned slice of memory in the allocator in the same page.
  // ///
  // /// Compared to [`alloc_bytes_owned`](Self::alloc_bytes_owned), this method only allocates from the main memory, so
  // /// the it means that if main memory does not have enough space but the freelist has segments can hold the size,
  // /// this method will still return an error.
  // ///
  // /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes_within_page`](Allocator::alloc_bytes_within_page).
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // fn alloc_bytes_owned_within_page(&self, size: u32) -> Result<BytesMut<Self>, Error> {
  //   self.alloc_bytes_within_page(size).map(|mut b| b.to_owned())
  // }

  // /// Allocates a slice of memory in the allocator in the same page.
  // ///
  // /// Compared to [`alloc_bytes`](Allocator::alloc_bytes), this method only allocates from the main memory, so
  // /// the it means that if main memory does not have enough space but the freelist has segments can hold the size,
  // /// this method will still return an error.
  // ///
  // /// The [`BytesRefMut`](crate::BytesRefMut) is zeroed out.
  // ///
  // /// If you want a [`BytesMut`](crate::BytesMut), see [`alloc_bytes_owned_within_page`](Allocator::alloc_bytes_owned_within_page).
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // fn alloc_bytes_within_page(&self, size: u32) -> Result<BytesRefMut<'_, Self>, Error>;

  /// Allocates a `T` in the allocator. Like [`alloc`](Allocator::alloc), but returns an `Owned`.
  ///
  /// The cost is one more atomic operation than [`alloc`](Allocator::alloc).
  ///
  /// ## Safety
  ///
  /// - See [`alloc`](Allocator::alloc) for safety.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  ///
  /// unsafe {
  ///   let mut data = arena.alloc_owned::<u64>().unwrap();
  ///   data.write(10);
  ///
  ///   assert_eq!(*data.as_ref(), 10);
  /// }
  /// ```
  unsafe fn alloc_owned<T>(&self) -> Result<Owned<T, Self>, Error> {
    self.alloc::<T>().map(|mut r| r.to_owned())
  }

  // /// Allocates a `T` in the allocator in the same page. Like [`alloc_within_page`](Allocator::alloc_within_page), but returns an `Owned`.
  // ///
  // /// ## Safety
  // /// - See [`alloc`](Allocator::alloc) for safety.
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // unsafe fn alloc_owned_within_page<T>(&self) -> Result<Owned<T, Self>, Error> {
  //   self.alloc_within_page::<T>().map(|mut r| r.to_owned())
  // }

  // /// Allocates a `T` in the allocator in the same page.
  // ///
  // /// ## Safety
  // ///
  // /// - See [`alloc`](Allocator::alloc) for safety.
  // #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  // #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  // unsafe fn alloc_within_page<T>(&self) -> Result<RefMut<'_, T, Self>, Error>;

  /// Returns the number of bytes allocated by the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let allocated = arena.allocated();
  /// ```
  fn allocated(&self) -> usize;

  /// Returns the whole main memory of the allocator as a byte slice.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let memory = arena.allocated_memory();
  /// ```
  #[inline]
  fn allocated_memory(&self) -> &[u8] {
    let allocated = self.allocated();
    unsafe { core::slice::from_raw_parts(self.raw_ptr(), allocated) }
  }

  /// Returns the start pointer of the main memory of the allocator.
  fn raw_mut_ptr(&self) -> *mut u8;

  /// Returns the start pointer of the main memory of the allocator.
  fn raw_ptr(&self) -> *const u8;

  /// Returns the capacity of the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let capacity = arena.capacity();
  /// ```
  #[inline]
  fn capacity(&self) -> usize {
    self.as_ref().cap() as usize
  }

  /// Clear the allocator.
  ///
  /// ## Safety
  /// - The current pointers get from the allocator cannot be used anymore after calling this method.
  /// - This method is not thread-safe.
  ///
  /// ## Examples
  ///
  /// Undefine behavior:
  ///
  /// ```ignore
  /// let mut data = arena.alloc::<Vec<u8>>().unwrap();
  ///
  /// arena.clear();
  ///
  /// data.write(vec![1, 2, 3]); // undefined behavior
  /// ```
  ///
  /// Good practice:
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  ///
  /// unsafe {
  ///   let mut data = arena.alloc::<Vec<u8>>().unwrap();
  ///   data.write(vec![1, 2, 3]);
  ///
  ///   arena.clear().unwrap();
  /// }
  ///
  /// ```
  unsafe fn clear(&self) -> Result<(), Error>;

  /// Returns the data offset of the allocator. The offset is the end of the reserved bytes of the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let data_offset = arena.data_offset();
  /// ```
  #[inline]
  fn data_offset(&self) -> usize {
    self.as_ref().data_offset()
  }

  /// Returns the data section of the allocator as a byte slice, header is not included.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let data = arena.data();
  /// ```
  #[inline]
  fn data(&self) -> &[u8] {
    unsafe {
      let offset = self.data_offset();
      let ptr = self.raw_ptr().add(offset);
      let allocated = self.allocated();
      core::slice::from_raw_parts(ptr, allocated - offset)
    }
  }

  /// Deallocates the memory at the given offset and size, the `offset..offset + size` will be made to a segment,
  /// returns `true` if the deallocation is successful.
  ///
  /// ## Safety
  /// - you must ensure the same `offset..offset + size` is not deallocated twice.
  /// - `offset` must be larger than the [`Allocator::data_offset`].
  /// - `offset + size` must be less than the [`Allocator::allocated`].
  unsafe fn dealloc(&self, offset: u32, size: u32) -> bool;

  /// Discards all freelist nodes in the allocator.
  ///
  /// Returns the number of bytes discarded.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// arena.discard_freelist();
  /// ```
  fn discard_freelist(&self) -> Result<u32, Error>;

  /// Returns the number of bytes discarded by the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let discarded = arena.discarded();
  /// ```
  fn discarded(&self) -> u32;

  /// Flushes the memory-mapped file to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.flush().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush(&self) -> std::io::Result<()> {
    self.as_ref().flush()
  }

  /// Flushes the memory-mapped file to disk asynchronously.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  ///
  /// arena.flush_async().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_async(&self) -> std::io::Result<()> {
    self.as_ref().flush_async()
  }

  /// Flushes outstanding memory map modifications in the range to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.flush_range(0, 100).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.as_ref().flush_range(offset, len)
  }

  /// Asynchronously flushes outstanding memory map modifications in the range to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  ///
  /// arena.flush_async_range(0, 100).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.as_ref().flush_async_range(offset, len)
  }

  /// Flushes outstanding memory map modifications in `Allocator`'s header to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.flush_header().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_header(&self) -> std::io::Result<()> {
    self.flush_header_and_range(0, 0)
  }

  /// Asynchronously flushes outstanding memory map modifications `Allocator`'s header to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  ///
  /// arena.flush_async_header().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_async_header(&self) -> std::io::Result<()> {
    self.flush_async_header_and_range(0, 0)
  }

  /// Flushes outstanding memory map modifications in the range and `Allocator`'s header to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.flush_header_and_range(0, 100).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_header_and_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.as_ref().flush_header_and_range(offset, len)
  }

  /// Asynchronously flushes outstanding memory map modifications in the range and `Allocator`'s header to disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  ///
  /// arena.flush_async_header_and_range(0, 100).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn flush_async_header_and_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.as_ref().flush_async_header_and_range(offset, len)
  }

  /// Returns a pointer to the memory at the given offset.
  ///
  /// ## Safety
  /// - `offset` must be less than the capacity of the allocator.
  #[inline]
  unsafe fn get_pointer(&self, offset: usize) -> *const u8 {
    if offset == 0 {
      return self.raw_ptr();
    }

    self.raw_ptr().add(offset)
  }

  /// Returns a pointer to the memory at the given offset.
  /// If the allocator is read-only, then this method will return a null pointer.
  ///
  /// ## Safety
  /// - `offset` must be less than the capacity of the allocator.
  ///
  /// # Panic
  /// - If the allocator is read-only, then this method will panic.
  #[inline]
  unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8 {
    assert!(!self.read_only(), "ARENA is read-only");

    if offset == 0 {
      return self.raw_mut_ptr();
    }

    self.raw_mut_ptr().add(offset)
  }

  /// Returns an aligned pointer to the memory at the given offset.
  ///
  /// ## Safety
  /// - `offset..offset + mem::size_of::<T>() + padding` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  #[inline]
  unsafe fn get_aligned_pointer<T>(&self, offset: usize) -> *const T {
    if offset == 0 {
      return core::ptr::null();
    }

    let align_offset = align_offset::<T>(offset as u32) as usize;
    self.raw_ptr().add(align_offset).cast()
  }

  /// Returns an aligned pointer to the memory at the given offset.
  /// If the allocator is read-only, then this method will return a null pointer.
  ///
  /// ## Safety
  /// - `offset..offset + mem::size_of::<T>() + padding` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  ///
  /// # Panic
  /// - If the allocator is read-only, then this method will panic.
  unsafe fn get_aligned_pointer_mut<T>(&self, offset: usize) -> core::ptr::NonNull<T> {
    assert!(!self.read_only(), "ARENA is read-only");

    if offset == 0 {
      return NonNull::dangling();
    }

    let align_offset = align_offset::<T>(offset as u32) as usize;
    let ptr = self.raw_mut_ptr().add(align_offset).cast();
    NonNull::new_unchecked(ptr)
  }

  /// Returns a bytes slice from the allocator.
  ///
  /// ## Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  /// - `size` must be less than the capacity of the allocator.
  /// - `offset + size` must be less than the capacity of the allocator.
  unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
    if size == 0 {
      return &[];
    }

    let ptr = self.get_pointer(offset);
    core::slice::from_raw_parts(ptr, size)
  }

  /// Returns a `u8` from the allocator.
  fn get_u8(&self, offset: usize) -> Result<u8, Error> {
    let allocated = self.allocated();
    if offset >= allocated {
      return Err(Error::OutOfBounds { offset, allocated });
    }

    let buf = unsafe {
      let ptr = self.raw_ptr().add(offset);
      core::slice::from_raw_parts(ptr, 1)
    };

    Ok(buf[0])
  }

  /// Returns a `i8` from the allocator.
  fn get_i8(&self, offset: usize) -> Result<i8, Error> {
    let allocated = self.allocated();
    if offset >= allocated {
      return Err(Error::OutOfBounds { offset, allocated });
    }

    let buf = unsafe {
      let ptr = self.raw_ptr().add(offset);
      core::slice::from_raw_parts(ptr, 1)
    };

    Ok(buf[0] as i8)
  }

  /// Returns a `u8` from the allocator without bounds checking.
  ///
  /// ## Safety
  /// - `offset + size` must be within the allocated memory of the allocator.
  unsafe fn get_u8_unchecked(&self, offset: usize) -> u8 {
    let buf = unsafe {
      let ptr = self.raw_ptr().add(offset);
      core::slice::from_raw_parts(ptr, 1)
    };

    buf[0]
  }

  /// Returns a `i8` from the allocator without bounds checking.
  ///
  /// ## Safety
  /// - `offset + size` must be within the allocated memory of the allocator.
  unsafe fn get_i8_unchecked(&self, offset: usize) -> i8 {
    let buf = unsafe {
      let ptr = self.raw_ptr().add(offset);
      core::slice::from_raw_parts(ptr, 1)
    };

    buf[0] as i8
  }

  define_bytes_utils!(
    u16:"be",
    u16:"le",
    u32:"be",
    u32:"le",
    u64:"be",
    u64:"le",
    u128:"be",
    u128:"le",
    i16:"be",
    i16:"le",
    i32:"be",
    i32:"le",
    i64:"be",
    i64:"le",
    i128:"be",
    i128:"le",
  );

  define_leb128_utils!(
    i16:3,
    i32:5,
    i64:10,
    i128:19,
    u16:3,
    u32:5,
    u64:10,
    u128:19,
  );

  /// Returns a mutable bytes slice from the allocator.
  /// If the allocator is read-only, then this method will return an empty slice.
  ///
  /// ## Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  /// - `size` must be less than the capacity of the allocator.
  /// - `offset + size` must be less than the capacity of the allocator.
  ///
  /// # Panic
  /// - If the allocator is read-only, then this method will panic.
  #[allow(clippy::mut_from_ref)]
  unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8] {
    if size == 0 {
      return &mut [];
    }

    let ptr = self.get_pointer_mut(offset);
    core::slice::from_raw_parts_mut(ptr, size)
  }

  /// Forcelly increases the discarded bytes.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// arena.increase_discarded(100);
  /// ```
  fn increase_discarded(&self, size: u32);

  /// Returns `true` if the allocator is created through memory map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Allocator, Options};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let is_map = arena.is_map();
  /// assert_eq!(is_map, false);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn is_map(&self) -> bool {
    self.as_ref().flag.contains(MemoryFlags::MMAP)
  }

  /// Returns `true` if the allocator is on disk.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let is_ondisk = arena.is_ondisk();
  /// assert_eq!(is_ondisk, false);
  /// ```
  #[inline]
  fn is_ondisk(&self) -> bool {
    self.as_ref().flag.contains(MemoryFlags::ON_DISK)
  }

  /// Returns `true` if the allocator is in memory.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let is_inmemory = arena.is_inmemory();
  /// assert_eq!(is_inmemory, true);
  /// ```
  #[inline]
  fn is_inmemory(&self) -> bool {
    !self.is_ondisk()
  }

  /// Returns `true` if the allocator is on-disk and created through memory map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).map_anon::<Arena>().unwrap();
  /// let is_map_anon = arena.is_map_anon();
  /// assert_eq!(is_map_anon, true);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn is_map_anon(&self) -> bool {
    self.is_map() && !self.is_ondisk()
  }

  /// Returns `true` if the allocator is on-disk and created through memory map.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let is_map_file = arena.is_map_file();
  /// assert_eq!(is_map_file, false);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn is_map_file(&self) -> bool {
    self.is_map() && self.is_ondisk()
  }

  /// Locks the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.lock_exclusive().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn lock_exclusive(&self) -> std::io::Result<()> {
    self.as_ref().lock_exclusive()
  }

  /// Locks the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.lock_shared().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn lock_shared(&self) -> std::io::Result<()> {
    self.as_ref().lock_shared()
  }

  /// Returns the magic version of the allocator. This value can be used to check the compatibility for application using
  /// [`Allocator`].
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let magic_version = arena.magic_version();
  /// ```
  fn magic_version(&self) -> u16;

  /// Returns the whole main memory of the allocator as a byte slice.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let memory = arena.memory();
  /// ```
  #[inline]
  fn memory(&self) -> &[u8] {
    unsafe { core::slice::from_raw_parts(self.raw_ptr(), self.capacity()) }
  }

  /// Calculates the checksum of the allocated memory (excluding the reserved memory specified by users through [`Options::with_reserved`]) of the allocator.
  fn checksum<S: BuildChecksumer>(&self, cks: &S) -> u64 {
    let allocated_memory = self.allocated_memory(); // Get the memory to be checksummed
    let reserved = self.reserved_slice().len();
    let data = &allocated_memory[reserved..];

    let page_size = self.page_size(); // Get the size of each page

    let total_len = data.len(); // Total length of the allocated memory
    let full_pages = total_len / page_size; // Calculate how many full pages there are
    let remaining_bytes = total_len % page_size; // Calculate the number of remaining bytes

    let mut hasher = cks.build_checksumer(); // Create the hasher

    // Iterate over each full page
    for page_id in 0..full_pages {
      let start = page_id * page_size;
      let end = start + page_size;

      // Feed each page's slice into the hasher
      hasher.update(&data[start..end]);
    }

    // Handle any remaining bytes that don’t fill a full page
    if remaining_bytes > 0 {
      let start = full_pages * page_size;
      hasher.update(&data[start..total_len]); // Process the remaining bytes
    }

    // Finalize and return the checksum
    hasher.digest()
  }

  /// Returns the minimum segment size of the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let min_segment_size = arena.minimum_segment_size();
  /// ```
  fn minimum_segment_size(&self) -> u32;

  /// Sets the minimum segment size of the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// arena.set_minimum_segment_size(100);
  /// ```
  fn set_minimum_segment_size(&self, size: u32);

  /// Returns `true` if the allocator is unify memory layout.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// assert_eq!(arena.unify(), false);
  ///
  /// let arena = Options::new().with_capacity(100).with_unify(true).alloc::<Arena>().unwrap();
  /// assert_eq!(arena.unify(), true);
  /// ```
  #[inline]
  fn unify(&self) -> bool {
    self.as_ref().unify()
  }

  /// Returns the path of the mmap file, only returns `Some` when the ARENA is backed by a mmap file.
  ///
  /// ## Example
  ///
  /// ```rust
  /// # use rarena_allocator::{unsync::Arena, Allocator, Options};
  ///
  /// # let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let path = arena.path();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn path(&self) -> Option<&Self::Path>;

  /// `mlock(ptr, len)`—Lock memory into RAM.
  ///
  /// ## Safety
  ///
  /// This function operates on raw pointers, but it should only be used on
  /// memory which the caller owns. Technically, locking memory shouldn't violate
  /// any invariants, but since unlocking it can violate invariants, this
  /// function is also unsafe for symmetry.
  ///
  /// Some implementations implicitly round the memory region out to the nearest
  /// page boundaries, so this function may lock more memory than explicitly
  /// requested if the memory isn't page-aligned. Other implementations fail if
  /// the memory isn't page-aligned.
  ///
  /// # References
  ///  - [POSIX]
  ///  - [Linux]
  ///  - [Apple]
  ///  - [FreeBSD]
  ///  - [NetBSD]
  ///  - [OpenBSD]
  ///  - [DragonFly BSD]
  ///  - [illumos]
  ///  - [glibc]
  ///
  /// [POSIX]: https://pubs.opengroup.org/onlinepubs/9699919799/functions/mlock.html
  /// [Linux]: https://man7.org/linux/man-pages/man2/mlock.2.html
  /// [Apple]: https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/mlock.2.html
  /// [FreeBSD]: https://man.freebsd.org/cgi/man.cgi?query=mlock&sektion=2
  /// [NetBSD]: https://man.netbsd.org/mlock.2
  /// [OpenBSD]: https://man.openbsd.org/mlock.2
  /// [DragonFly BSD]: https://man.dragonflybsd.org/?command=mlock&section=2
  /// [illumos]: https://illumos.org/man/3C/mlock
  /// [glibc]: https://www.gnu.org/software/libc/manual/html_node/Page-Lock-Functions.html#index-mlock
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.as_ref().mlock(offset, len)
  }

  /// `munlock(ptr, len)`—Unlock memory.
  ///
  /// ## Safety
  ///
  /// This function operates on raw pointers, but it should only be used on
  /// memory which the caller owns, to avoid compromising the `mlock` invariants
  /// of other unrelated code in the process.
  ///
  /// Some implementations implicitly round the memory region out to the nearest
  /// page boundaries, so this function may unlock more memory than explicitly
  /// requested if the memory isn't page-aligned.
  ///
  /// # References
  ///  - [POSIX]
  ///  - [Linux]
  ///  - [Apple]
  ///  - [FreeBSD]
  ///  - [NetBSD]
  ///  - [OpenBSD]
  ///  - [DragonFly BSD]
  ///  - [illumos]
  ///  - [glibc]
  ///
  /// [POSIX]: https://pubs.opengroup.org/onlinepubs/9699919799/functions/munlock.html
  /// [Linux]: https://man7.org/linux/man-pages/man2/munlock.2.html
  /// [Apple]: https://developer.apple.com/library/archive/documentation/System/Conceptual/ManPages_iPhoneOS/man2/munlock.2.html
  /// [FreeBSD]: https://man.freebsd.org/cgi/man.cgi?query=munlock&sektion=2
  /// [NetBSD]: https://man.netbsd.org/munlock.2
  /// [OpenBSD]: https://man.openbsd.org/munlock.2
  /// [DragonFly BSD]: https://man.dragonflybsd.org/?command=munlock&section=2
  /// [illumos]: https://illumos.org/man/3C/munlock
  /// [glibc]: https://www.gnu.org/software/libc/manual/html_node/Page-Lock-Functions.html#index-munlock
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  unsafe fn munlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    self.as_ref().munlock(offset, len)
  }

  /// Returns the offset to the start of the allocator.
  ///
  /// ## Safety
  /// - `ptr` must be allocated by this allocator.
  unsafe fn offset(&self, ptr: *const u8) -> usize;

  /// Returns the page size.
  ///
  /// If in no-std environment, then this method will return `4096`.
  /// Otherwise, it will return the system's page size.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let page_size = arena.page_size();
  /// ```
  fn page_size(&self) -> usize;

  /// Returns `true` if the arena is read-only.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let read_only = arena.read_only();
  /// ```
  #[inline]
  fn read_only(&self) -> bool {
    self.as_ref().read_only()
  }

  /// Returns the number of references to the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let refs = arena.refs();
  /// ```
  fn refs(&self) -> usize;

  /// Returns the number of bytes remaining bytes can be allocated by the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let remaining = arena.remaining();
  /// ```
  fn remaining(&self) -> usize;

  /// Sets remove on drop, only works on mmap with a file backend.
  ///
  /// Default is `false`.
  ///
  /// > **WARNING:** Once set to `true`, the backed file will be removed when the allocator is dropped, even though the file is opened in
  /// > read-only mode.
  ///
  /// ## Example
  ///
  /// ```rust
  /// # use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// # let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// arena.remove_on_drop(true);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn remove_on_drop(&self, remove_on_drop: bool) {
    self.as_ref().set_remove_on_drop(remove_on_drop);
  }

  /// Set back the allocator's main memory cursor to the given position.
  ///
  /// ## Safety
  /// - If the current position is larger than the given position,
  ///   then the memory between the current position and the given position will be reclaimed,
  ///   so must ensure the memory chunk between the current position and the given position will not
  ///   be accessed anymore.
  /// - This method is not thread safe.
  unsafe fn rewind(&self, pos: ArenaPosition);

  /// Try to lock the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.try_lock_exclusive().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn try_lock_exclusive(&self) -> std::io::Result<()> {
    self.as_ref().try_lock_exclusive()
  }

  /// Try to lock the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.try_lock_shared().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn try_lock_shared(&self) -> std::io::Result<()> {
    self.as_ref().try_lock_shared()
  }

  /// Unlocks the underlying file, only works on mmap with a file backend.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  ///
  ///
  /// let mut arena = unsafe { Options::new().with_create_new(true).with_read(true).with_write(true).with_capacity(100).map_mut::<Arena, _>(&path).unwrap() };
  /// arena.lock_exclusive().unwrap();
  ///
  /// // do some thing
  /// arena.unlock().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn unlock(&self) -> std::io::Result<()> {
    self.as_ref().unlock()
  }

  /// Returns the version of the allocator.
  ///
  /// ## Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Options, Allocator};
  ///
  /// let arena = Options::new().with_capacity(100).alloc::<Arena>().unwrap();
  /// let version = arena.version();
  /// ```
  fn version(&self) -> u16;
}
