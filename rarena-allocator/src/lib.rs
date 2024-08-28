#![doc = include_str!("../README.md")]
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]

#[cfg(not(any(feature = "std", feature = "alloc")))]
compile_error!("`rarena-allocator` requires either the 'std' or 'alloc' feature to be enabled");

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

mod error;
pub use error::*;

mod options;
pub use options::*;

use core::mem;

pub use either;

const FREELIST_OFFSET: usize = 1;
const FREELIST_SIZE: usize = mem::size_of::<Freelist>();
const MAGIC_TEXT: [u8; 2] = *b"al";
const MAGIC_TEXT_OFFSET: usize = FREELIST_OFFSET + FREELIST_SIZE;
const MAGIC_TEXT_SIZE: usize = MAGIC_TEXT.len();
const MAGIC_VERISON_OFFSET: usize = MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE;
const MAGIC_VERISON_SIZE: usize = mem::size_of::<u16>();
const VERSION_OFFSET: usize = MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE;
const VERSION_SIZE: usize = mem::size_of::<u16>();
const CURRENT_VERSION: u16 = 0;
const SENTINEL_SEGMENT_NODE_OFFSET: u32 = u32::MAX;
const SENTINEL_SEGMENT_NODE_SIZE: u32 = u32::MAX;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
static PAGE_SIZE: std::sync::LazyLock<u32> = std::sync::LazyLock::new(|| {
  #[cfg(not(windows))]
  {
    rustix::param::page_size() as u32
  }

  #[cfg(windows)]
  {
    use winapi::um::sysinfoapi::{GetSystemInfo, SYSTEM_INFO};

    unsafe {
      let mut system_info: SYSTEM_INFO = std::mem::zeroed();
      GetSystemInfo(&mut system_info);
      system_info.dwPageSize
    }
  }
});

/// Enumeration of possible methods to seek within an [`Arena`] allocator.
///
#[derive(Copy, PartialEq, Eq, Clone, Debug)]
pub enum ArenaPosition {
  /// Sets the offset to the provided number of bytes.
  Start(u32),

  /// Sets the offset to the capacity of the allocator minus the provided number of bytes.
  End(u32),

  /// Sets the offset to the current position plus the specified number of
  /// bytes.
  ///
  /// It is possible to seek beyond the end of an object, but it's an error to
  /// seek before byte 0.
  Current(i64),
}

bitflags::bitflags! {
  #[derive(Clone, Copy)]
  struct MemoryFlags: u8 {
    const ON_DISK = 0b0000_0001;
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    const MMAP = 0b0000_0010;
  }
}

/// The memory chunk allocated from the allocator.
pub trait Memory {
  /// Returns how many bytes of accessible memory occupies.
  fn capacity(&self) -> usize;

  /// Returns the accessible offset to the pointer of the allocator.
  fn offset(&self) -> usize;

  /// Returns how many bytes of the whole memory occupies.
  fn memory_capacity(&self) -> usize;

  /// Returns the offset to the pointer of the allocator.
  fn memory_offset(&self) -> usize;

  /// Detach the value from the ARENA, which means when the value is dropped,
  /// the underlying memory will not be collected for futhur allocation.
  ///
  /// # Safety
  /// - The caller must ensure the value is dropped before the ARENA is dropped.
  unsafe fn detach(&mut self);

  /// Flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush(&self) -> std::io::Result<()>;

  /// Asynchronously flush the buffer to the disk.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async(&self) -> std::io::Result<()>;
}

mod sealed {
  pub trait Sealed: Sized + Clone {}
}

#[inline]
fn write_sanity(freelist: u8, magic_version: u16, data: &mut [u8]) {
  data[FREELIST_OFFSET] = freelist;
  data[MAGIC_TEXT_OFFSET..MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE].copy_from_slice(MAGIC_TEXT.as_ref());
  data[MAGIC_VERISON_OFFSET..MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE]
    .copy_from_slice(magic_version.to_le_bytes().as_ref());
  data[VERSION_OFFSET..VERSION_OFFSET + VERSION_SIZE]
    .copy_from_slice(CURRENT_VERSION.to_le_bytes().as_ref());
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn sanity_check(
  freelist: Option<Freelist>,
  magic_version: u16,
  data: &[u8],
) -> std::io::Result<Freelist> {
  let stored_freelist = data[FREELIST_OFFSET];
  let stored_freelist = Freelist::try_from(stored_freelist).map_err(invalid_data)?;

  if let Some(freelist) = freelist {
    if stored_freelist != freelist {
      return Err(bad_freelist());
    }
  }

  let stored_magic_version: u16 = u16::from_le_bytes(
    data[MAGIC_VERISON_OFFSET..MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE]
      .try_into()
      .unwrap(),
  );
  let version: u16 = u16::from_le_bytes(
    data[VERSION_OFFSET..VERSION_OFFSET + VERSION_SIZE]
      .try_into()
      .unwrap(),
  );

  if stored_magic_version != magic_version {
    return Err(invalid_data(MagicVersionMismatch::new(
      magic_version,
      stored_magic_version,
    )));
  }

  if version != CURRENT_VERSION {
    return Err(invalid_data(VersionMismatch::new(CURRENT_VERSION, version)));
  }

  if data[MAGIC_TEXT_OFFSET..MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE] != MAGIC_TEXT {
    return Err(bad_magic());
  }
  Ok(stored_freelist)
}

/// A trait for easily interacting with the sync and unsync allocator allocators.
pub trait Allocator: sealed::Sealed {
  /// Returns the reserved bytes of the allocator specified in the [`ArenaOptions::with_reserved`].
  fn reserved_slice(&self) -> &[u8];

  /// Returns the mutable reserved bytes of the allocator specified in the [`ArenaOptions::with_reserved`].
  ///
  /// # Safety
  /// - The caller need to make sure there is no data-race
  #[allow(clippy::mut_from_ref)]
  unsafe fn reserved_slice_mut(&self) -> &mut [u8];

  /// Allocates a `T` in the allocator.
  ///
  /// # Safety
  ///
  /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`](Allocator::RefMut::detach),
  ///   then the caller must ensure that the `T` is dropped before the allocator is dropped.
  ///   Otherwise, it will lead to memory leaks.
  ///
  /// - If this is file backed allocator, then `T` must be recoverable from bytes.
  ///   1. Types require allocation are not recoverable.
  ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
  ///      although those types are on stack, but they cannot be recovered, when reopens the file.
  ///
  /// # Examples
  ///
  /// ## Memory leak
  ///
  /// The following example demonstrates the memory leak when the `T` is a heap allocated type and detached.
  ///
  /// ```ignore
  ///
  /// let arena = Arena::new(ArenaOptions::new());
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
  /// let arena = Arena::map_mut("path/to/file", ArenaOptions::new(), OpenOptions::create_new(Some(1000)).read(true).write(true), MmapOptions::default()).unwrap();
  ///
  /// let mut data = arena.alloc::<TypeOnHeap>().unwrap();
  /// data.detach();
  /// data.write(TypeOnHeap { data: vec![1, 2, 3] });
  /// let offset = data.offset();
  /// drop(arena);
  ///
  /// // reopen the file
  /// let arena = Arena::map("path/to/file", OpenOptions::read(true), MmapOptions::default()).unwrap();
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
  /// let arena = Arena::new(ArenaOptions::new());
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
  /// let arena = Arena::map_mut("path/to/file", ArenaOptions::new(), OpenOptions::create_new(Some(1000)).read(true).write(true), MmapOptions::default()).unwrap();
  ///
  /// let mut data = arena.alloc::<Recoverable>().unwrap();
  /// data.write(Recoverable { field1: 10, field2: AtomicU32::new(20) });
  /// data.detach();
  /// let offset = data.offset();
  /// drop(arena);
  ///
  /// // reopen the file
  /// let arena = Arena::map("path/to/file", OpenOptions::read(true), MmapOptions::default()).unwrap();
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
  /// # Example
  ///
  /// ```ignore
  /// let mut bytes = arena.alloc_aligned_bytes::<T>(extra).unwrap();
  /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  /// ```
  fn alloc_aligned_bytes<T>(&self, size: u32) -> Result<BytesRefMut<Self>, Error>;

  /// Allocates an owned byte slice that can hold a well-aligned `T` and extra `size` bytes.
  ///
  /// The layout of the allocated memory is:
  ///
  /// ```text
  /// | T | [u8; size] |
  /// ```
  ///
  /// # Example
  ///
  /// ```ignore
  /// let mut bytes = arena.alloc_aligned_bytes_owned::<T>(extra).unwrap();
  /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  /// ```
  fn alloc_aligned_bytes_owned<T>(&self, size: u32) -> Result<BytesMut<Self>, Error>;

  /// Allocates an owned byte slice that can hold a well-aligned `T` and extra `size` bytes.
  ///
  /// The layout of the allocated memory is:
  ///
  /// ```text
  /// | T | [u8; size] |
  /// ```
  ///
  /// # Example
  ///
  /// ```ignore
  /// let mut bytes = arena.alloc_aligned_bytes_owned_within_page::<T>(extra).unwrap();
  /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn alloc_aligned_bytes_owned_within_page<T>(&self, size: u32) -> Result<BytesMut<Self>, Error>;

  /// Allocates a byte slice that can hold a well-aligned `T` and extra `size` bytes within a page.
  ///
  /// The layout of the allocated memory is:
  ///
  /// ```text
  /// | T | [u8; size] |
  /// ```
  ///
  /// # Example
  ///
  /// ```ignore
  /// let mut bytes = arena.alloc_aligned_bytes_within_page::<T>(extra).unwrap();
  /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn alloc_aligned_bytes_within_page<T>(&self, size: u32) -> Result<BytesRefMut<Self>, Error>;

  /// Allocates a slice of memory in the allocator.
  ///
  /// The [`BytesRefMut`](Allocator::BytesRefMut) is zeroed out.
  ///
  /// If you want a [`BytesMut`](Allocator::BytesMut), see [`alloc_bytes_owned`](Allocator::alloc_bytes_owned).
  fn alloc_bytes(&self, size: u32) -> Result<BytesRefMut<Self>, Error>;

  /// Allocates an owned slice of memory in the allocator.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes`](Allocator::alloc_bytes).
  fn alloc_bytes_owned(&self, size: u32) -> Result<BytesMut<Self>, Error>;

  /// Allocates an owned slice of memory in the allocator in the same page.
  ///
  /// Compared to [`alloc_bytes_owned`](Self::alloc_bytes_owned), this method only allocates from the main memory, so
  /// the it means that if main memory does not have enough space but the freelist has segments can hold the size,
  /// this method will still return an error.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes_within_page`](Allocator::alloc_bytes_within_page).
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn alloc_bytes_owned_within_page(&self, size: u32) -> Result<BytesMut<Self>, Error>;

  /// Allocates a slice of memory in the allocator in the same page.
  ///
  /// Compared to [`alloc_bytes`](Allocator::alloc_bytes), this method only allocates from the main memory, so
  /// the it means that if main memory does not have enough space but the freelist has segments can hold the size,
  /// this method will still return an error.
  ///
  /// The [`BytesRefMut`](Allocator::BytesRefMut) is zeroed out.
  ///
  /// If you want a [`BytesMut`](Allocator::BytesMut), see [`alloc_bytes_owned_within_page`](Allocator::alloc_bytes_owned_within_page).
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn alloc_bytes_within_page(&self, size: u32) -> Result<BytesRefMut<Self>, Error>;

  /// Allocates a `T` in the allocator. Like [`alloc`](Allocator::alloc), but returns an `Owned`.
  ///
  /// The cost is one more atomic operation than [`alloc`](Allocator::alloc).
  ///
  /// # Safety
  ///
  /// - See [`alloc`](Allocator::alloc) for safety.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  ///
  /// unsafe {
  ///   let mut data = arena.alloc_owned::<u64>().unwrap();
  ///   data.write(10);
  ///
  ///   assert_eq!(*data.as_ref(), 10);
  /// }
  /// ```
  unsafe fn alloc_owned<T>(&self) -> Result<Owned<T, Self>, Error>;

  /// Allocates a `T` in the allocator in the same page. Like [`alloc_within_page`](Allocator::alloc_within_page), but returns an `Owned`.
  ///
  /// # Safety
  /// - See [`alloc`](Allocator::alloc) for safety.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  unsafe fn alloc_owned_within_page<T>(&self) -> Result<Owned<T, Self>, Error>;

  /// Allocates a `T` in the allocator in the same page.
  ///
  /// # Safety
  ///
  /// - See [`alloc`](Allocator::alloc) for safety.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  unsafe fn alloc_within_page<T>(&self) -> Result<RefMut<'_, T, Self>, Error>;

  /// Returns the number of bytes allocated by the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let allocated = arena.allocated();
  /// ```
  fn allocated(&self) -> usize;

  /// Returns the whole main memory of the allocator as a byte slice.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let memory = arena.allocated_memory();
  /// ```
  fn allocated_memory(&self) -> &[u8];

  /// Returns the start pointer of the main memory of the allocator.
  fn raw_mut_ptr(&self) -> *mut u8;

  /// Returns the start pointer of the main memory of the allocator.
  fn raw_ptr(&self) -> *const u8;

  /// Returns the capacity of the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let capacity = arena.capacity();
  /// ```
  fn capacity(&self) -> usize;

  /// Clear the allocator.
  ///
  /// # Safety
  /// - The current pointers get from the allocator cannot be used anymore after calling this method.
  /// - This method is not thread-safe.
  ///
  /// # Examples
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
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
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
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let data_offset = arena.data_offset();
  /// ```
  fn data_offset(&self) -> usize;

  /// Returns the data section of the allocator as a byte slice, header is not included.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let data = arena.data();
  /// ```
  fn data(&self) -> &[u8];

  /// Deallocates the memory at the given offset and size, the `offset..offset + size` will be made to a segment,
  /// returns `true` if the deallocation is successful.
  ///
  /// # Safety
  /// - you must ensure the same `offset..offset + size` is not deallocated twice.
  /// - `offset` must be larger than the [`Allocator::data_offset`].
  /// - `offset + size` must be less than the [`Allocator::allocated`].
  unsafe fn dealloc(&self, offset: u32, size: u32) -> bool;

  /// Discards all freelist nodes in the allocator.
  ///
  /// Returns the number of bytes discarded.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// arena.discard_freelist();
  /// ```
  fn discard_freelist(&self) -> Result<u32, Error>;

  /// Returns the number of bytes discarded by the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let discarded = arena.discarded();
  /// ```
  fn discarded(&self) -> u32;

  /// Flushes the memory-mapped file to disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, OpenOptions, MmapOptions, Allocator};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// arena.flush().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush(&self) -> std::io::Result<()>;

  /// Flushes the memory-mapped file to disk asynchronously.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let open_options = OpenOptions::default().create(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  ///
  /// arena.flush_async().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async(&self) -> std::io::Result<()>;

  /// Flushes outstanding memory map modifications in the range to disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// arena.flush_range(0, 100).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_range(&self, offset: usize, len: usize) -> std::io::Result<()>;

  /// Asynchronously flushes outstanding memory map modifications in the range to disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  /// let open_options = OpenOptions::default().create(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  ///
  /// arena.flush_async_range(0, 100).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()>;

  /// Returns a pointer to the memory at the given offset.
  ///
  /// # Safety
  /// - `offset` must be less than the capacity of the allocator.
  unsafe fn get_pointer(&self, offset: usize) -> *const u8;

  /// Returns a pointer to the memory at the given offset.
  /// If the allocator is read-only, then this method will return a null pointer.
  ///
  /// # Safety
  /// - `offset` must be less than the capacity of the allocator.
  ///
  /// # Panic
  /// - If the allocator is read-only, then this method will panic.
  unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8;

  /// Returns an aligned pointer to the memory at the given offset.
  ///
  /// # Safety
  /// - `offset..offset + mem::size_of::<T>() + padding` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  unsafe fn get_aligned_pointer<T>(&self, offset: usize) -> *const T;

  /// Returns an aligned pointer to the memory at the given offset.
  /// If the allocator is read-only, then this method will return a null pointer.
  ///
  /// # Safety
  /// - `offset..offset + mem::size_of::<T>() + padding` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  ///
  /// # Panic
  /// - If the allocator is read-only, then this method will panic.
  unsafe fn get_aligned_pointer_mut<T>(&self, offset: usize) -> core::ptr::NonNull<T>;

  /// Returns a bytes slice from the allocator.
  ///
  /// # Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  /// - `size` must be less than the capacity of the allocator.
  /// - `offset + size` must be less than the capacity of the allocator.
  unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8];

  /// Returns a mutable bytes slice from the allocator.
  /// If the allocator is read-only, then this method will return an empty slice.
  ///
  /// # Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the allocator.
  /// - `size` must be less than the capacity of the allocator.
  /// - `offset + size` must be less than the capacity of the allocator.
  ///
  /// # Panic
  /// - If the allocator is read-only, then this method will panic.
  #[allow(clippy::mut_from_ref)]
  unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8];

  /// Forcelly increases the discarded bytes.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// arena.increase_discarded(100);
  /// ```
  fn increase_discarded(&self, size: u32);

  /// Returns `true` if the allocator is created through memory map.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let is_mmap = arena.is_mmap();
  /// assert_eq!(is_mmap, false);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn is_mmap(&self) -> bool;

  /// Returns `true` if the allocator is on disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let is_ondisk = arena.is_ondisk();
  /// assert_eq!(is_ondisk, false);
  /// ```
  fn is_ondisk(&self) -> bool;

  /// Returns `true` if the allocator is on-disk and created through memory map.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let is_ondisk_and_mmap = arena.is_ondisk_and_mmap();
  /// assert_eq!(is_ondisk_and_mmap, false);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn is_ondisk_and_mmap(&self) -> bool;

  /// Locks the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// arena.lock_exclusive().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn lock_exclusive(&self) -> std::io::Result<()>;

  /// Locks the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// arena.lock_shared().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn lock_shared(&self) -> std::io::Result<()>;

  /// Returns the magic version of the allocator. This value can be used to check the compatibility for application using
  /// [`Arena`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let magic_version = arena.magic_version();
  /// ```
  fn magic_version(&self) -> u16;

  /// Opens a read only allocator backed by a mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  ///   # let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  ///   # let mmap_options = MmapOptions::new();
  ///   # let arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map(&path, open_options, mmap_options, 0).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self>;

  /// Opens a read only allocator backed by a mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  ///   # let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  ///   # let mmap_options = MmapOptions::new();
  ///   # let arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map_with_path_builder::<_, std::io::Error>(|| Ok(path.to_path_buf()), open_options, mmap_options, 0).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>;

  /// Creates a new allocator backed by an anonymous mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, MmapOptions};
  ///
  /// let mmap_options = MmapOptions::new().len(100);
  /// let arena = Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_anon(opts: ArenaOptions, mmap_options: MmapOptions) -> std::io::Result<Self>;

  /// Creates a new allocator backed by a copy-on-write memory map backed by a file.
  ///
  /// Data written to the allocator will not be visible by other processes, and will not be carried through to the underlying file.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map_copy(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_copy<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self>;

  /// Creates a new allocator backed by a copy-on-write memory map backed by a file with the given path builder.
  ///
  /// Data written to the allocator will not be visible by other processes, and will not be carried through to the underlying file.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map_copy_with_path_builder::<_, std::io::Error>(|| Ok(path.to_path_buf()), ArenaOptions::new(), open_options, mmap_options).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_copy_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>;

  /// Opens a read only allocator backed by a copy-on-write read-only memory map backed by a file.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  ///   # let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  ///   # let mmap_options = MmapOptions::new();
  ///   # let arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map_copy_read_only(&path, ArenaOptions::new(), open_options, mmap_options, 0).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_copy_read_only<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self>;

  /// Opens a read only allocator backed by a copy-on-write read-only memory map backed by a file with the given path builder.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// # {
  ///   # let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  ///   # let mmap_options = MmapOptions::new();
  ///   # let arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// # }
  ///
  /// let open_options = OpenOptions::default().read(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map_copy_read_only_with_path_builder::<_, std::io::Error>(|| Ok(path.to_path_buf()), ArenaOptions::new(), open_options, mmap_options, 0).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_copy_read_only_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>;

  /// Creates a new allocator backed by a mmap with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self>;

  /// Creates a new allocator backed by a mmap with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  ///
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let arena = Arena::map_mut_with_path_builder::<_, std::io::Error>(|| Ok(path.to_path_buf()), ArenaOptions::new(), open_options, mmap_options).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn map_mut_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, either::Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>;

  /// Returns the whole main memory of the allocator as a byte slice.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let memory = arena.memory();
  /// ```
  fn memory(&self) -> &[u8];

  /// Returns the minimum segment size of the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let min_segment_size = arena.minimum_segment_size();
  /// ```
  fn minimum_segment_size(&self) -> u32;

  /// Sets the minimum segment size of the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// arena.set_minimum_segment_size(100);
  /// ```
  fn set_minimum_segment_size(&self, size: u32);

  /// `mlock(ptr, len)`—Lock memory into RAM.
  ///
  /// # Safety
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
  #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
  #[cfg_attr(
    docsrs,
    doc(cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows))))
  )]
  unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()>;

  /// `munlock(ptr, len)`—Unlock memory.
  ///
  /// # Safety
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
  #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
  #[cfg_attr(
    docsrs,
    doc(cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows))))
  )]
  unsafe fn munlock(&self, offset: usize, len: usize) -> std::io::Result<()>;

  /// Creates a new allocator with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// ```
  fn new(opts: ArenaOptions) -> Self;

  /// Returns the offset to the start of the allocator.
  ///
  /// # Safety
  /// - `ptr` must be allocated by this allocator.
  unsafe fn offset(&self, ptr: *const u8) -> usize;

  /// Returns the page size.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let page_size = arena.page_size();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn page_size(&self) -> usize;

  /// Returns `true` if the arena is read-only.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let read_only = arena.read_only();
  /// ```
  fn read_only(&self) -> bool;

  /// Returns the number of references to the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let refs = arena.refs();
  /// ```
  fn refs(&self) -> usize;

  /// Returns the number of bytes remaining bytes can be allocated by the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
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
  /// # Example
  ///
  /// ```rust
  /// # use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// # let arena = Arena::new(ArenaOptions::new());
  /// arena.remove_on_drop(true);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn remove_on_drop(&self, remove_on_drop: bool);

  /// Set back the allocator's main memory cursor to the given position.
  ///
  /// # Safety
  /// - If the current position is larger than the given position,
  ///   then the memory between the current position and the given position will be reclaimed,
  ///   so must ensure the memory chunk between the current position and the given position will not
  ///   be accessed anymore.
  /// - This method is not thread safe.
  unsafe fn rewind(&self, pos: ArenaPosition);

  /// Try to lock the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// arena.try_lock_exclusive().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn try_lock_exclusive(&self) -> std::io::Result<()>;

  /// Try to lock the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// arena.try_lock_shared().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn try_lock_shared(&self) -> std::io::Result<()>;

  /// Unlocks the underlying file, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator, OpenOptions, MmapOptions};
  /// # let path = tempfile::NamedTempFile::new().unwrap().into_temp_path();
  /// # std::fs::remove_file(&path);
  ///
  /// let open_options = OpenOptions::default().create_new(Some(100)).read(true).write(true);
  /// let mmap_options = MmapOptions::new();
  /// let mut arena = Arena::map_mut(&path, ArenaOptions::new(), open_options, mmap_options).unwrap();
  /// arena.lock_exclusive().unwrap();
  ///
  /// // do some thing
  /// arena.unlock().unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  fn unlock(&self) -> std::io::Result<()>;

  /// Returns the version of the allocator.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{sync::Arena, ArenaOptions, Allocator};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let version = arena.version();
  /// ```
  fn version(&self) -> u16;
}

mod common {
  use core::{mem, ptr};

  #[cfg(not(feature = "loom"))]
  pub(crate) use core::cell::UnsafeCell;
  #[cfg(not(feature = "loom"))]
  pub(crate) use std::alloc::{alloc_zeroed, dealloc, Layout};

  #[cfg(feature = "loom")]
  pub(crate) use loom::{
    alloc::{alloc_zeroed, dealloc, Layout},
    cell::UnsafeCell,
  };

  #[cfg(not(feature = "loom"))]
  pub(crate) use core::sync::atomic::*;

  #[cfg(feature = "loom")]
  pub(crate) use loom::sync::atomic::*;

  pub(crate) trait UnsafeCellExt<T> {
    fn as_inner_ptr(&self) -> *const T;
    fn as_inner_mut(&self) -> *mut T;
    #[inline]
    fn as_inner_ref(&self) -> &T {
      unsafe { &*self.as_inner_ptr() }
    }
    #[inline]
    #[allow(clippy::mut_from_ref)]
    fn as_inner_ref_mut(&self) -> &mut T {
      unsafe { &mut *self.as_inner_mut() }
    }
  }

  impl<T> UnsafeCellExt<T> for core::cell::UnsafeCell<T> {
    #[inline]
    fn as_inner_ptr(&self) -> *const T {
      self.get()
    }

    #[inline]
    fn as_inner_mut(&self) -> *mut T {
      self.get()
    }
  }

  #[cfg(feature = "loom")]
  impl<T> UnsafeCellExt<T> for loom::cell::UnsafeCell<T> {
    #[inline]
    fn as_inner_ptr(&self) -> *const T {
      unsafe { self.get().deref() }
    }

    #[inline]
    fn as_inner_mut(&self) -> *mut T {
      unsafe { self.get_mut().deref() }
    }
  }

  #[derive(Debug)]
  pub(super) struct AlignedVec {
    pub(super) ptr: ptr::NonNull<u8>,
    pub(super) cap: usize,
    pub(super) align: usize,
  }

  impl Drop for AlignedVec {
    #[inline]
    fn drop(&mut self) {
      if self.cap != 0 {
        unsafe {
          dealloc(self.ptr.as_ptr(), self.layout());
        }
      }
    }
  }

  impl AlignedVec {
    #[inline]
    pub(super) fn new<H>(capacity: usize, align: usize) -> Self {
      let align = align.max(mem::align_of::<H>());
      assert!(
        capacity <= Self::max_capacity(align),
        "`capacity` cannot exceed isize::MAX - {}",
        align - 1
      );

      let ptr = unsafe {
        let layout = Layout::from_size_align_unchecked(capacity, align);
        let ptr = alloc_zeroed(layout);
        if ptr.is_null() {
          std::alloc::handle_alloc_error(layout);
        }
        ptr::NonNull::new_unchecked(ptr)
      };

      Self {
        ptr,
        cap: capacity,
        align,
      }
    }

    #[inline]
    pub(super) const fn max_capacity(align: usize) -> usize {
      isize::MAX as usize - (align - 1)
    }

    #[inline]
    pub(super) const fn layout(&self) -> std::alloc::Layout {
      unsafe { std::alloc::Layout::from_size_align_unchecked(self.cap, self.align) }
    }

    #[inline]
    pub(super) fn as_mut_ptr(&mut self) -> *mut u8 {
      self.ptr.as_ptr()
    }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn invalid_data<E: std::error::Error + Send + Sync + 'static>(e: E) -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, e)
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn reserved_too_large() -> std::io::Error {
  std::io::Error::new(
    std::io::ErrorKind::InvalidInput,
    "reserved memory too large, the remaining memory is not enough to construct the ARENA",
  )
}

#[inline]
const fn panic_reserved_too_large() -> ! {
  panic!("reserved memory too large, the remaining memory is not enough to construct the ARENA")
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn bad_magic() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "arena has bad magic")
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn bad_freelist() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "freelist mismatch")
}

#[inline]
const fn decode_segment_node(val: u64) -> (u32, u32) {
  ((val >> 32) as u32, val as u32)
}

#[inline]
const fn encode_segment_node(size: u32, next: u32) -> u64 {
  ((size as u64) << 32) | next as u64
}

/// Calculates the aligned offset for a given type `T` starting from `current_offset`.
///
/// This function aligns the given `current_offset` to the next boundary that satisfies the alignment requirements of type `T`.
///
/// # Parameters
///
/// - `current_offset`: The initial offset that needs to be aligned.
///
/// # Returns
///
/// The aligned offset that is the next multiple of the alignment requirement of type `T`.
///
/// # Examples
///
/// ```ignore
/// use std::mem;
///
/// #[repr(C, align(8))]
/// struct Meta {
///     a: u64,
///     b: u64,
/// }
///
/// let initial_offset: u32 = 1;
/// let aligned_offset = align_offset::<Meta>(initial_offset);
/// assert_eq!(aligned_offset, 8);
/// ```
///
/// # Explanation
///
/// - Given an `alignment` of type `T`, this function calculates the next aligned offset from `current_offset`.
/// - It ensures that the result is a multiple of `alignment` by adding `alignment - 1` to `current_offset` and then clearing the lower bits using bitwise AND with the negation of `alignment - 1`.
///
/// ```ignore
/// let alignment = mem::align_of::<T>() as u32;
/// (current_offset + alignment - 1) & !(alignment - 1)
/// ```
#[inline]
pub const fn align_offset<T>(current_offset: u32) -> u32 {
  let alignment = core::mem::align_of::<T>() as u32;
  (current_offset + alignment - 1) & !(alignment - 1)
}

#[inline(never)]
#[cold]
fn abort() -> ! {
  #[cfg(feature = "std")]
  {
    std::process::abort()
  }

  #[cfg(not(feature = "std"))]
  {
    struct Abort;
    impl Drop for Abort {
      fn drop(&mut self) {
        panic!();
      }
    }
    let _a = Abort;
    panic!("abort");
  }
}

#[cfg(feature = "std")]
macro_rules! write_byte_order {
  ($write_name:ident::$put_name:ident::$converter:ident($ty:ident, $endian:literal)) => {
    paste::paste! {
      #[doc = "Write a `" $ty "` value into the buffer in " $endian " byte order, return an error if the buffer does not have enough space."]
      #[inline]
      #[cfg(feature = "std")]
      pub fn $write_name(&mut self, value: $ty) -> std::io::Result<()> {
        self.$put_name(value).map_err(|e| std::io::Error::new(std::io::ErrorKind::WriteZero, e))
      }
    }
  }
}

macro_rules! put_byte_order {
  ($name:ident::$converter:ident($ty:ident, $endian:literal)) => {
    paste::paste! {
      #[doc = "Put a `" $ty "` value into the buffer in " $endian " byte order, return an error if the buffer does not have enough space."]
      #[inline]
      pub fn $name(&mut self, value: $ty) -> Result<(), BufferTooSmall> {
        const SIZE: usize = core::mem::size_of::<$ty>();

        if self.len + SIZE > self.capacity() {
          return Err(BufferTooSmall {
            remaining: self.capacity() - self.len,
            want: SIZE,
          });
        }

        // SAFETY: We have checked the buffer size.
        unsafe { self. [< $name _unchecked >](value); }
        Ok(())
      }

      #[doc = "Put a `" $ty "` value into the buffer in " $endian " byte order, without doing bounds checking."]
      ///
      #[doc = "For a safe alternative see [`" $name "`](Self::" $name ")."]
      ///
      /// # Safety
      ///
      /// Calling this method if the buffer does not have enough space to hold the value is *[undefined behavior]*.
      ///
      /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
      #[inline]
      pub unsafe fn [< $name _unchecked >] (&mut self, value: $ty) {
        const SIZE: usize = core::mem::size_of::<$ty>();

        let cur = self.len;
        let buf = self.buffer_mut();
        buf[cur..cur + SIZE].copy_from_slice(&value.$converter());
        self.len += SIZE;
      }
    }
  }
}

macro_rules! impl_bytes_mut_utils {
  (align) => {
    /// Add paddings to the buffer according to the alignment of `T`.
    ///
    /// Returns a well-aligned pointer for `T`
    #[inline]
    pub fn align_to<T>(&mut self) -> Result<core::ptr::NonNull<T>, BufferTooSmall> {
      if mem::size_of::<T>() == 0 {
        return Ok(core::ptr::NonNull::dangling());
      }

      let align_offset = crate::align_offset::<T>(self.allocated.memory_offset + self.len as u32);

      if align_offset > self.allocated.memory_offset + self.allocated.memory_size {
        return Err(BufferTooSmall {
          remaining: self.allocated.memory_size as usize - self.len,
          want: align_offset as usize - self.len - self.allocated.memory_offset as usize,
        });
      }

      self.len = (align_offset - self.allocated.memory_offset) as usize;
      // SAFETY: We have checked the buffer size, and apply the align
      Ok(unsafe {
        core::ptr::NonNull::new_unchecked(self.as_mut_ptr().add(self.len).cast::<T>())
      })
    }


    /// Put `T` into the buffer, return an error if the buffer does not have enough space.
    ///
    /// You may want to use [`put_aligned`] instead of this method.
    ///
    /// # Safety
    ///
    /// - Must invoke [`align_to`] before invoking this method, if `T` is not ZST.
    /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`],
    ///   then the caller must ensure that the `T` is dropped before the allocator is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed allocator, then `T` must be recoverable from bytes.
    ///   1. Types require allocation are not recoverable.
    ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
    ///      although those types are on stack, but they cannot be recovered, when reopens the file.
    pub unsafe fn put<T>(&mut self, val: T) -> Result<&mut T, BufferTooSmall> {
      let size = core::mem::size_of::<T>();

      if self.len + size > self.capacity() {
        return Err(BufferTooSmall {
          remaining: self.capacity() - self.len,
          want: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      let ptr = self.as_mut_ptr().add(self.len).cast::<T>();
      ptr.write(val);
      self.len += size;
      Ok(&mut *ptr)
    }

    /// Put `T` into the buffer, return an error if the buffer does not have enough space.
    ///
    /// # Safety
    ///
    /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`],
    ///   then the caller must ensure that the `T` is dropped before the allocator is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed allocator, then `T` must be recoverable from bytes.
    ///   1. Types require allocation are not recoverable.
    ///   2. Pointers are not recoverable, like `*const T`, `*mut T`, `NonNull` and any structs contains pointers,
    ///      although those types are on stack, but they cannot be recovered, when reopens the file.
    pub unsafe fn put_aligned<T>(&mut self, val: T) -> Result<&mut T, BufferTooSmall> {
      let mut ptr = self.align_to::<T>()?;

      ptr.as_ptr().write(val);
      self.len += ::core::mem::size_of::<T>();
      Ok(ptr.as_mut())
    }
  };
  (slice) => {
    /// Put a bytes slice into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_slice(&mut self, slice: &[u8]) -> Result<(), BufferTooSmall> {
      let size = slice.len();

      if self.len + size > self.capacity() {
        return Err(BufferTooSmall {
          remaining: self.capacity() - self.len,
          want: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { self.put_slice_unchecked(slice); }
      Ok(())
    }

    /// Put a bytes slice into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_slice`](Self::put_slice).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough space to hold the slice is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn put_slice_unchecked(&mut self, slice: &[u8]) {
      let size = slice.len();
      let cur = self.len;
      let buf = self.buffer_mut();
      buf[cur..cur + size].copy_from_slice(slice);
      self.len += size;
    }
  };
  ($($ty:ident), +$(,)?) => {
    $(
      paste::paste! {
        put_byte_order!([< put_ $ty _be>]::to_be_bytes($ty, "big-endian"));
        put_byte_order!([< put_ $ty _le >]::to_le_bytes($ty, "little-endian"));
        put_byte_order!([< put_ $ty _ne >]::to_ne_bytes($ty, "native-endian"));
        #[cfg(feature="std")]
        write_byte_order!([< write_ $ty _be>]::[< put_ $ty _be>]::to_be_bytes($ty, "big-endian"));
        #[cfg(feature="std")]
        write_byte_order!([< write_ $ty _le >]::[< put_ $ty _le >]::to_le_bytes($ty, "little-endian"));
        #[cfg(feature="std")]
        write_byte_order!([< write_ $ty _ne >]::[< put_ $ty _ne >]::to_ne_bytes($ty, "native-endian"));
      }
    )*
  };
  (8) => {
    /// Put a `u8` value into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_u8(&mut self, value: u8) -> Result<(), BufferTooSmall> {
      const SIZE: usize = core::mem::size_of::<u8>();

      if self.len + SIZE > self.capacity() {
        return Err(BufferTooSmall {
          remaining: self.capacity() - self.len,
          want: SIZE,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { self.put_u8_unchecked(value); }
      Ok(())
    }

    /// Put a `u8` value into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_u8`](Self::put_u8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough space to hold the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn put_u8_unchecked(&mut self, value: u8) {
      const SIZE: usize = core::mem::size_of::<u8>();

      let cur = self.len;
      let buf = self.buffer_mut();
      buf[cur..cur + SIZE].copy_from_slice(&[value]);
      self.len += SIZE;
    }

    /// Put a `i8` value into the buffer, return an error if the buffer does not have enough space.
    #[inline]
    pub fn put_i8(&mut self, value: i8) -> Result<(), BufferTooSmall> {
      self.put_u8(value as u8)
    }

    /// Put a `i8` value into the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`put_i8`](Self::put_i8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough space to hold the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn put_i8_unchecked(&mut self, value: i8) {
      self.put_u8_unchecked(value as u8)
    }
  };
}

macro_rules! get_byte_order {
  ($name:ident::$converter:ident($ty:ident, $endian:literal)) => {
    paste::paste! {
      #[doc = "Get a `" $ty "` value from the buffer in " $endian " byte order, return an error if the buffer does not have enough bytes."]
      #[inline]
      pub fn $name(&mut self) -> Result<$ty, NotEnoughBytes> {
        const SIZE: usize = core::mem::size_of::<$ty>();

        if self.len < SIZE {
          return Err(NotEnoughBytes {
            remaining: self.len,
            read: SIZE,
          });
        }

        // SAFETY: We have checked the buffer size.
        unsafe { Ok(self.[< $name _unchecked >]()) }
      }

      #[doc = "Get a `" $ty "` value from the buffer in " $endian " byte order, without doing bounds checking."]
      ///
      #[doc = "For a safe alternative see [`" $name "`](Self::" $name ")."]
      ///
      /// # Safety
      ///
      /// Calling this method if the buffer does not have enough bytes to read the value is *[undefined behavior]*.
      ///
      /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
      #[inline]
      pub unsafe fn [< $name _unchecked >](&mut self) -> $ty {
        const SIZE: usize = core::mem::size_of::<$ty>();

        let cur = self.len - SIZE;
        let buf = self.buffer();
        let value = <$ty>::from_be_bytes(buf[cur..cur + SIZE].try_into().unwrap());
        self.len -= SIZE;
        value
      }
    }
  }
}

macro_rules! impl_bytes_utils {
  (slice) => {
    /// Get a byte slice from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_slice(&self, size: usize) -> Result<&[u8], NotEnoughBytes> {
      if self.len < size {
        return Err(NotEnoughBytes {
          remaining: self.len,
          read: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_slice_unchecked(size)) }
    }

    /// Get a byte slice from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_slice`](Self::get_slice).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the slice is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_slice_unchecked(&self, size: usize) -> &[u8] {
      let buf = self.buffer();
      &buf[..size]
    }

    /// Get a mutable byte slice from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_slice_mut(&mut self, size: usize) -> Result<&mut [u8], NotEnoughBytes> {
      if self.len < size {
        return Err(NotEnoughBytes {
          remaining: self.len,
          read: size,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_slice_mut_unchecked(size)) }
    }

    /// Get a mutable byte slice from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_slice_mut`](Self::get_slice_mut).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the slice is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_slice_mut_unchecked(&mut self, size: usize) -> &mut [u8] {
      let buf = self.buffer_mut();
      &mut buf[..size]
    }
  };
  ($($ty:ident), +$(,)?) => {
    $(
      paste::paste! {
        get_byte_order!([< get_ $ty _be >]::from_be_bytes($ty, "big-endian"));
        get_byte_order!([< get_ $ty _le >]::from_le_bytes($ty, "little-endian"));
        get_byte_order!([< get_ $ty _ne >]::from_ne_bytes($ty, "native-endian"));
      }
    )*
  };
  (8) => {
    /// Get a `u8` value from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_u8(&mut self) -> Result<u8, NotEnoughBytes> {
      if self.len < 1 {
        return Err(NotEnoughBytes {
          remaining: self.len,
          read: 1,
        });
      }

      // SAFETY: We have checked the buffer size.
      unsafe { Ok(self.get_u8_unchecked()) }
    }

    /// Get a `u8` value from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_u8`](Self::get_u8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_u8_unchecked(&mut self) -> u8 {
      let cur = self.len - 1;
      let buf = self.buffer();
      let value = buf[cur];
      self.len -= 1;
      value
    }

    /// Get a `i8` value from the buffer, return an error if the buffer does not have enough bytes.
    #[inline]
    pub fn get_i8(&mut self) -> Result<i8, NotEnoughBytes> {
      self.get_u8().map(|v| v as i8)
    }

    /// Get a `i8` value from the buffer, without doing bounds checking.
    ///
    /// For a safe alternative see [`get_i8`](Self::get_i8).
    ///
    /// # Safety
    ///
    /// Calling this method if the buffer does not have enough bytes to read the value is *[undefined behavior]*.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    #[inline]
    pub unsafe fn get_i8_unchecked(&mut self) -> i8 {
      self.get_u8_unchecked() as i8
    }
  };
}

#[cfg(feature = "std")]
macro_rules! impl_write_in {
  () => {
    #[inline]
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
      self
        .put_slice(buf)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::WriteZero, e))
        .map(|_| buf.len())
    }

    #[inline(always)]
    fn flush(&mut self) -> std::io::Result<()> {
      Ok(())
    }
  };
}

macro_rules! impl_write {
  ($ident: ident) => {
    #[cfg(feature = "std")]
    impl std::io::Write for $ident {
      impl_write_in!();
    }
  };
  ($ident: ident<'a>) => {
    #[cfg(feature = "std")]
    impl<'a> std::io::Write for $ident<'a> {
      impl_write_in!();
    }
  };
  ($ident: ident<T>) => {
    #[cfg(feature = "std")]
    impl<T> std::io::Write for $ident<T> {
      impl_write_in!();
    }
  };
  ($ident: ident<A>) => {
    #[cfg(feature = "std")]
    impl<A: $crate::Allocator> std::io::Write for $ident<A> {
      impl_write_in!();
    }
  };
  ($ident: ident<'a, A>) => {
    #[cfg(feature = "std")]
    impl<'a, A: $crate::Allocator> std::io::Write for $ident<'a, A> {
      impl_write_in!();
    }
  };
}

/// The metadata of the structs allocated from ARENA.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Meta {
  parent_ptr: *const u8,
  memory_offset: u32,
  memory_size: u32,
  ptr_offset: u32,
  ptr_size: u32,
}

unsafe impl Send for Meta {}
unsafe impl Sync for Meta {}

impl Meta {
  #[inline]
  const fn null(parent_ptr: *const u8) -> Self {
    Self {
      parent_ptr,
      memory_offset: 0,
      memory_size: 0,
      ptr_offset: 0,
      ptr_size: 0,
    }
  }

  #[inline]
  const fn new(parent_ptr: *const u8, memory_offset: u32, memory_size: u32) -> Self {
    Self {
      parent_ptr,
      memory_offset,
      memory_size,
      // just set the ptr_offset to the memory_offset, and ptr_size to the memory_size.
      // we will align the ptr_offset and ptr_size when it should be aligned.
      ptr_offset: memory_offset,
      ptr_size: memory_size,
    }
  }

  #[inline]
  unsafe fn clear<A: Allocator>(&self, arena: &A) {
    let ptr = arena.raw_mut_ptr().add(self.ptr_offset as usize);
    core::ptr::write_bytes(ptr, 0, self.ptr_size as usize);
  }

  #[inline]
  fn align_to<T>(&mut self) {
    let align_offset = align_offset::<T>(self.memory_offset);
    self.ptr_offset = align_offset;
    self.ptr_size = mem::size_of::<T>() as u32;
  }

  #[inline]
  fn align_bytes_to<T>(&mut self) {
    let align_offset = align_offset::<T>(self.memory_offset);
    self.ptr_offset = align_offset;
    self.ptr_size = self.memory_offset + self.memory_size - self.ptr_offset;
  }
}

mod bytes;
pub use bytes::*;

mod object;
pub use object::*;

/// Lock-free allocator allocator can be used in concurrent environments.
pub mod sync;

/// allocator allocator for single-threaded environments.
pub mod unsync;
