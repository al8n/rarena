use core::{
  fmt,
  mem::{self, MaybeUninit},
  ops,
  ptr::{self, NonNull},
  slice,
};

use crossbeam_utils::Backoff;
use either::Either;

use crate::{common::*, error::*, ArenaOptions};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use crate::{MmapOptions, OpenOptions};

#[allow(unused_imports)]
use std::boxed::Box;

const OVERHEAD: usize = mem::size_of::<Header>();
const MAGIC_TEXT: [u8; 3] = *b"liu";
const MAGIC_TEXT_OFFSET: usize = VERSION_OFFSET + VERSION_SIZE;
const MAGIC_TEXT_SIZE: usize = MAGIC_TEXT.len();
const MAGIC_VERISON_OFFSET: usize = 1;
const MAGIC_VERISON_SIZE: usize = mem::size_of::<u16>();
const VERSION_OFFSET: usize = MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE;
const VERSION_SIZE: usize = mem::size_of::<u16>();
const CURRENT_VERSION: u16 = 0;


const SENTINEL_SEGMENT_NODE_SIZE: u32 = u32::MAX;
const SENTINEL_SEGMENT_NODE_OFFSET: u32 = u32::MAX;
const REMOVED_SEGMENT_NODE_SIZE: u32 = 0;

#[derive(Debug)]
struct AlignedVec {
  ptr: ptr::NonNull<u8>,
  cap: usize,
  align: usize,
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
  fn new(capacity: usize, align: usize) -> Self {
    let align = align.max(mem::align_of::<Header>());
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
  const fn max_capacity(align: usize) -> usize {
    isize::MAX as usize - (align - 1)
  }

  #[inline]
  fn layout(&self) -> std::alloc::Layout {
    unsafe { std::alloc::Layout::from_size_align_unchecked(self.cap, self.align) }
  }

  #[inline]
  fn as_mut_ptr(&mut self) -> *mut u8 {
    self.ptr.as_ptr()
  }
}

enum MemoryBackend {
  #[allow(dead_code)]
  Vec(AlignedVec),
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  MmapMut {
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    lock: bool,
    shrink_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  Mmap {
    buf: *mut memmap2::Mmap,
    file: std::fs::File,
    lock: bool,
    #[allow(dead_code)]
    shrink_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  AnonymousMmap {
    #[allow(dead_code)]
    buf: memmap2::MmapMut,
  },
}

#[derive(Debug)]
#[repr(C)]
struct Header {
  /// The sentinel node for the ordered free list.
  sentinel: AtomicU64,
  allocated: AtomicU32,
  min_segment_size: AtomicU32,
  discarded: AtomicU32,
}

impl Header {
  #[inline]
  fn new(size: u32, min_segment_size: u32) -> Self {
    Self {
      allocated: AtomicU32::new(size),
      sentinel: AtomicU64::new(encode_segment_node(SENTINEL_SEGMENT_NODE_OFFSET, SENTINEL_SEGMENT_NODE_SIZE)),
      min_segment_size: AtomicU32::new(min_segment_size),
      discarded: AtomicU32::new(0),
    }
  }
}

struct Memory {
  refs: AtomicUsize,
  cap: u32,
  data_offset: usize,
  header_ptr: Either<*mut u8, Header>,
  ptr: *mut u8,
  #[allow(dead_code)]
  backend: MemoryBackend,
  unify: bool,
  magic_version: u16,
  version: u16,
}

impl Memory {
  unsafe fn clear(&mut self) {
    let header_ptr_offset = self.ptr.align_offset(mem::align_of::<Header>());
    let data_offset = header_ptr_offset + mem::size_of::<Header>();

    let min_segment_size = self.header().min_segment_size.load(Ordering::Acquire);
    let (header, data_offset) = if self.unify {
      let header_ptr = self.ptr.add(header_ptr_offset);
      let header = header_ptr.cast::<Header>();
      header.write(Header::new(data_offset as u32, min_segment_size));
      (Either::Left(header_ptr), data_offset)
    } else {
      (Either::Right(Header::new(1, min_segment_size)), 1)
    };

    self.header_ptr = header;
    self.data_offset = data_offset;
  }

  fn new_vec(opts: ArenaOptions) -> Self {
    let cap = opts.capacity();
    let alignment = opts.maximum_alignment();
    let min_segment_size = opts.minimum_segment_size();
    let unify = opts.unify();

    let cap = if unify {
      cap.saturating_add(OVERHEAD as u32)
    } else {
      cap.saturating_add(alignment as u32)
    } as usize;

    let mut vec = AlignedVec::new(cap, alignment);
    // Safety: we have add the overhead for the header
    unsafe {
      let ptr = vec.as_mut_ptr();
      ptr::write_bytes(ptr, 0, vec.cap);

      let header_ptr_offset = ptr.add(1).align_offset(mem::align_of::<Header>()) + 1;
      let data_offset = header_ptr_offset + mem::size_of::<Header>();
      let header_ptr = ptr.add(header_ptr_offset).cast::<Header>();

      let (header, data_offset) = if unify {
        Self::write_sanify(opts.magic_version(), slice::from_raw_parts_mut(ptr, 8));
        header_ptr.write(Header::new(data_offset as u32, min_segment_size));
        (Either::Left(header_ptr as _), data_offset)
      } else {
        (Either::Right(Header::new(1, min_segment_size)), 1)
      };

      Self {
        cap: cap as u32,
        refs: AtomicUsize::new(1),
        ptr,
        header_ptr: header,
        backend: MemoryBackend::Vec(vec),
        data_offset,
        unify,
        magic_version: opts.magic_version(),
        version: CURRENT_VERSION,
      }
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    alignment: usize,
    min_segment_size: u32,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    let (create_new, file) = open_options.open(path.as_ref())?;

    unsafe {
      mmap_options.map_mut(&file).and_then(|mut mmap| {
        let cap = mmap.len();
        if cap < OVERHEAD {
          return Err(invalid_data(TooSmall::new(cap, OVERHEAD)));
        }

        // TODO:  should we align the memory?
        let _alignment = alignment.max(mem::align_of::<Header>());

        let ptr = mmap.as_mut_ptr();

        let header_ptr_offset = ptr.add(1).align_offset(mem::align_of::<Header>()) + 1;
        let data_offset = header_ptr_offset + mem::size_of::<Header>();
        let header_ptr = ptr.add(header_ptr_offset).cast::<Header>();

        let (version, magic_version) = if create_new {
          // initialize the memory with 0
          ptr::write_bytes(ptr, 0, cap);

          Self::write_sanify(
            magic_version,
            slice::from_raw_parts_mut(ptr, header_ptr_offset),
          );

          // Safety: we have add the overhead for the header
          header_ptr.write(Header::new(data_offset as u32, min_segment_size));

          (CURRENT_VERSION, magic_version)
        } else {
          let allocated = (*header_ptr).allocated.load(Ordering::Acquire);
          ptr::write_bytes(
            ptr.add(allocated as usize),
            0,
            mmap.len() - allocated as usize,
          );
          Self::sanity_check(magic_version, &mmap)?;
          (CURRENT_VERSION, magic_version)
        };

        let this = Self {
          cap: cap as u32,
          backend: MemoryBackend::MmapMut {
            buf: Box::into_raw(Box::new(mmap)),
            file,
            lock: open_options.is_lock(),
            shrink_on_drop: open_options.is_shrink_on_drop(),
          },
          header_ptr: Either::Left(header_ptr as _),
          ptr,
          refs: AtomicUsize::new(1),
          data_offset,
          unify: true,
          magic_version,
          version,
        };

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    use either::Either;

    if !path.as_ref().exists() {
      return Err(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "file not found",
      ));
    }

    let (_, file) = open_options.open(path.as_ref())?;

    unsafe {
      mmap_options.map(&file).and_then(|mmap| {
        let len = mmap.len();
        if len < OVERHEAD {
          return Err(invalid_data(TooSmall::new(len, OVERHEAD)));
        }

        Self::sanity_check(magic_version, &mmap)?;

        let ptr = mmap.as_ptr();
        let header_ptr_offset = ptr.align_offset(mem::align_of::<Header>());
        let data_offset = header_ptr_offset + mem::size_of::<Header>();
        let header_ptr = ptr.add(header_ptr_offset) as _;
        let this = Self {
          cap: len as u32,
          backend: MemoryBackend::Mmap {
            buf: Box::into_raw(Box::new(mmap)),
            file,
            lock: open_options.is_lock(),
            shrink_on_drop: open_options.is_shrink_on_drop(),
          },
          header_ptr: Either::Left(header_ptr),
          ptr: ptr as _,
          refs: AtomicUsize::new(1),
          data_offset,
          unify: true,
          magic_version,
          version: CURRENT_VERSION,
        };

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_anon(
    mmap_options: MmapOptions,
    alignment: usize,
    min_segment_size: u32,
    unify: bool,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    mmap_options.map_anon().and_then(|mut mmap| {
      if unify {
        if mmap.len() < OVERHEAD {
          return Err(invalid_data(TooSmall::new(mmap.len(), OVERHEAD)));
        }
      } else if mmap.len() < alignment {
        return Err(invalid_data(TooSmall::new(mmap.len(), alignment)));
      }

      // TODO:  should we align the memory?
      let _alignment = alignment.max(mem::align_of::<Header>());
      let ptr = mmap.as_mut_ptr();

      // Safety: we have add the overhead for the header
      unsafe {
        ptr::write_bytes(ptr, 0, mmap.len());

        let header_ptr_offset = ptr.add(1).align_offset(mem::align_of::<Header>()) + 1;
        let data_offset = header_ptr_offset + mem::size_of::<Header>();
        let header_ptr = ptr.add(header_ptr_offset);

        let (header, data_offset) = if unify {
          Self::write_sanify(
            magic_version,
            slice::from_raw_parts_mut(ptr, header_ptr_offset),
          );
          header_ptr
            .cast::<Header>()
            .write(Header::new(data_offset as u32, min_segment_size));
          (Either::Left(header_ptr as _), data_offset)
        } else {
          (Either::Right(Header::new(1, min_segment_size)), 1)
        };

        let this = Self {
          cap: mmap.len() as u32,
          backend: MemoryBackend::AnonymousMmap { buf: mmap },
          refs: AtomicUsize::new(1),
          data_offset,
          header_ptr: header,
          ptr,
          unify,
          magic_version,
          version: CURRENT_VERSION,
        };

        Ok(this)
      }
    })
  }

  #[inline]
  fn write_sanify(magic_version: u16, data: &mut [u8]) {
    data[MAGIC_VERISON_OFFSET..MAGIC_VERISON_OFFSET + MAGIC_VERISON_SIZE]
      .copy_from_slice(magic_version.to_le_bytes().as_ref());
    data[VERSION_OFFSET..VERSION_OFFSET + VERSION_SIZE]
      .copy_from_slice(CURRENT_VERSION.to_le_bytes().as_ref());
    data[MAGIC_TEXT_OFFSET..MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE]
      .copy_from_slice(MAGIC_TEXT.as_ref());
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  fn sanity_check(magic_version: u16, data: &[u8]) -> std::io::Result<()> {
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
    Ok(())
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush() },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_async(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush_async() },
      _ => Ok(()),
    }
  }

  #[allow(dead_code)]
  #[inline]
  const fn as_ptr(&self) -> *const u8 {
    self.ptr
  }

  #[inline]
  const fn as_mut_ptr(&self) -> *mut u8 {
    self.ptr
  }

  #[inline]
  fn header(&self) -> &Header {
    unsafe {
      match &self.header_ptr {
        Either::Left(header_ptr) => &*(*header_ptr).cast::<Header>(),
        Either::Right(header) => header,
      }
    }
  }

  #[inline]
  const fn cap(&self) -> u32 {
    self.cap
  }

  /// Only works on mmap with a file backend, unmounts the memory mapped file and truncates it to the specified size.
  ///
  /// ## Safety:
  /// - This method must be invoked in the drop impl of `Arena`.
  unsafe fn unmount(&mut self) {
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    match &self.backend {
      MemoryBackend::MmapMut {
        buf,
        file,
        lock,
        shrink_on_drop,
        ..
      } => {
        use fs4::FileExt;

        // we must trigger the drop of the mmap
        let used = if *shrink_on_drop {
          let header = self.header();
          Some(header.allocated.load(Ordering::Acquire))
        } else {
          None
        };

        let _ = Box::from_raw(*buf);

        if let Some(used) = used {
          if used < self.cap {
            let _ = file.set_len(used as u64);
          }
        }

        let _ = file.sync_all();

        if *lock {
          let _ = file.unlock();
        }
      }
      MemoryBackend::Mmap {
        lock,
        file,
        shrink_on_drop,
        buf,
        ..
      } => {
        use fs4::FileExt;

        // Any errors during unmapping/closing are ignored as the only way
        // to report them would be through panicking which is highly discouraged
        // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97

        let used = if *shrink_on_drop {
          let header = self.header();
          Some(header.allocated.load(Ordering::Acquire))
        } else {
          None
        };

        let _ = Box::from_raw(*buf);

        if let Some(used) = used {
          if used < self.cap {
            let _ = file.set_len(used as u64);
            let _ = file.sync_all();
          }
        }

        // relaxed ordering is enough here as we're in a drop, no one else can
        // access this memory anymore.
        if *lock {
          let _ = file.unlock();
        }
      }
      _ => {}
    }
  }
}

#[derive(Debug, Default, Copy, Clone)]
struct Allocated {
  memory_offset: u32,
  memory_size: u32,
  ptr_offset: u32,
  ptr_size: u32,
}

impl Allocated {
  #[inline]
  const fn null() -> Self {
    Self {
      memory_offset: 0,
      memory_size: 0,
      ptr_offset: 0,
      ptr_size: 0,
    }
  }

  #[inline]
  const fn new(memory_offset: u32, memory_size: u32) -> Self {
    Self {
      memory_offset,
      memory_size,
      // just set the ptr_offset to the memory_offset, and ptr_size to the memory_size.
      // we will align the ptr_offset and ptr_size when it should be aligned.
      ptr_offset: memory_offset,
      ptr_size: memory_size,
    }
  }

  #[inline]
  unsafe fn clear(&self, arena: &Arena) {
    let ptr = arena.ptr.add(self.memory_offset as usize);
    ptr::write_bytes(ptr, 0, self.memory_size as usize);
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
    self.ptr_size = self.memory_size - self.ptr_offset;
  }
}

/// Arena should be lock-free
pub struct Arena {
  ptr: *mut u8,
  data_offset: u32,
  max_retries: u8,
  inner: NonNull<Memory>,
  unify: bool,
  magic_version: u16,
  version: u16,
  ro: bool,
  cap: u32,
}

impl fmt::Debug for Arena {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let header = self.header();
    let allocated = header.allocated.load(Ordering::Acquire);

    // Safety:
    // The ptr is always non-null, we only deallocate it when the ARENA is dropped.
    let data = unsafe { slice::from_raw_parts(self.ptr, (allocated - self.data_offset) as usize) };

    f.debug_struct("Arena")
      .field("cap", &self.cap)
      .field("header", header)
      .field("data", &data)
      .finish()
  }
}

impl Clone for Arena {
  fn clone(&self) -> Self {
    unsafe {
      let memory = self.inner.as_ref();

      let old_size = memory.refs.fetch_add(1, Ordering::Release);
      if old_size > usize::MAX >> 1 {
        abort();
      }

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last Arena is dropped.
      Self {
        max_retries: self.max_retries,
        magic_version: self.magic_version,
        version: self.version,
        ptr: self.ptr,
        data_offset: self.data_offset,
        ro: self.ro,
        inner: self.inner,
        unify: self.unify,
        cap: self.cap,
      }
    }
  }
}

impl Arena {
  /// Returns the version of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let version = arena.version();
  /// ```
  #[inline]
  pub const fn version(&self) -> u16 {
    self.version
  }

  /// Returns the magic version of the ARENA. This value can be used to check the compatibility for application using
  /// [`Arena`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let magic_version = arena.magic_version();
  /// ```
  #[inline]
  pub const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Returns the number of bytes allocated by the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let allocated = arena.allocated();
  /// ```
  #[inline]
  pub fn allocated(&self) -> usize {
    self.header().allocated.load(Ordering::Acquire) as usize
  }

  /// Returns the capacity of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let capacity = arena.capacity();
  /// ```
  #[inline]
  pub const fn capacity(&self) -> usize {
    self.cap as usize
  }

  /// Returns the number of bytes remaining bytes can be allocated by the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let remaining = arena.remaining();
  /// ```
  #[inline]
  pub fn remaining(&self) -> usize {
    (self.cap as usize).saturating_sub(self.allocated())
  }

  /// Returns the number of references to the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let refs = arena.refs();
  /// ```
  #[inline]
  pub fn refs(&self) -> usize {
    unsafe { self.inner.as_ref().refs.load(Ordering::Acquire) }
  }

  /// Returns the number of bytes discarded by the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let discarded = arena.discarded();
  /// ```
  #[inline]
  pub fn discarded(&self) -> u32 {
    self.header().discarded.load(Ordering::Acquire)
  }

  /// Forcelly increases the discarded bytes.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// arena.increase_discarded(100);
  /// ```
  #[inline]
  pub fn increase_discarded(&self, size: u32) {
    self.header().discarded.fetch_add(size, Ordering::Release);
  }

  /// Returns the minimum segment size of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let min_segment_size = arena.minimum_segment_size();
  /// ```
  #[inline]
  pub fn minimum_segment_size(&self) -> u32 {
    self.header().min_segment_size.load(Ordering::Acquire)
  }

  /// Sets the minimum segment size of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// arena.set_minimum_segment_size(100);
  /// ```
  #[inline]
  pub fn set_minimum_segment_size(&self, size: u32) {
    self
      .header()
      .min_segment_size
      .store(size, Ordering::Release);
  }

  /// Returns the data offset of the ARENA. The offset is the end of the ARENA header.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let data_offset = arena.data_offset();
  /// ```
  #[inline]
  pub const fn data_offset(&self) -> usize {
    self.data_offset as usize
  }

  /// Returns the data section of the ARENA as a byte slice, header is not included.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let data = arena.data();
  /// ```
  #[inline]
  pub fn data(&self) -> &[u8] {
    unsafe {
      let ptr = self.ptr.add(self.data_offset as usize);
      let allocated = self.header().allocated.load(Ordering::Acquire);
      slice::from_raw_parts(ptr, (allocated - self.data_offset) as usize)
    }
  }

  /// Returns the whole allocated memory of the ARENA as a byte slice.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let allocated_memory = arena.allocated_memory();
  /// ```
  #[inline]
  pub fn allocated_memory(&self) -> &[u8] {
    unsafe {
      let allocated = self.header().allocated.load(Ordering::Acquire);
      slice::from_raw_parts(self.ptr, allocated as usize)
    }
  }

  /// Returns the whole memory of the ARENA as a byte slice.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let memory = arena.memory();
  /// ```
  #[inline]
  pub const fn memory(&self) -> &[u8] {
    unsafe { slice::from_raw_parts(self.ptr, self.cap as usize) }
  }

  /// Returns `true` if the arena is read-only.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let read_only = arena.read_only();
  /// ```
  #[inline]
  pub const fn read_only(&self) -> bool {
    self.ro
  }

  #[inline]
  fn header(&self) -> &Header {
    // Safety:
    // The inner is always non-null, we only deallocate it when the ARENA is dropped.
    unsafe { (*self.inner.as_ptr()).header() }
  }
}

unsafe impl Send for Arena {}
unsafe impl Sync for Arena {}

impl Arena {
  /// Creates a new ARENA with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// ```
  #[inline]
  pub fn new(opts: ArenaOptions) -> Self {
    let memory = Memory::new_vec(opts);
    Self::new_in(memory, opts.maximum_retries(), opts.unify(), false)
  }

  /// Creates a new ARENA backed by a mmap with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  pub fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Memory::map_mut(
      path,
      open_options,
      mmap_options,
      opts.maximum_alignment(),
      opts.minimum_segment_size(),
      opts.magic_version(),
    )
    .map(|memory| Self::new_in(memory, opts.maximum_retries(), true, false))
  }

  /// Opens a read only ARENA backed by a mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  pub fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Memory::map(path, open_options, mmap_options, magic_version)
      .map(|memory| Self::new_in(memory, 0, true, true))
  }

  /// Creates a new ARENA backed by an anonymous mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions, MmapOptions};
  ///
  /// let mmap_options = MmapOptions::new().len(100);
  /// let arena = Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub fn map_anon(opts: ArenaOptions, mmap_options: MmapOptions) -> std::io::Result<Self> {
    Memory::map_anon(
      mmap_options,
      opts.maximum_alignment(),
      opts.minimum_segment_size(),
      opts.unify(),
      opts.magic_version(),
    )
    .map(|memory| Self::new_in(memory, opts.maximum_retries(), opts.unify(), false))
  }

  /// Flushes the memory-mapped file to disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions, OpenOptions, MmapOptions};
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
  pub fn flush(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().flush() }
  }

  /// Flushes the memory-mapped file to disk asynchronously.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions, OpenOptions, MmapOptions};
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
  pub fn flush_async(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().flush_async() }
  }

  /// Allocates an owned slice of memory in the ARENA.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes`](Self::alloc_bytes).
  #[inline]
  pub fn alloc_bytes_owned(&self, size: u32) -> Result<BytesMut, Error> {
    self.alloc_bytes(size).map(|mut b| b.to_owned())
  }

  /// Allocates a slice of memory in the ARENA.
  ///
  /// The [`BytesRefMut`] is zeroed out.
  ///
  /// If you want a [`BytesMut`], see [`alloc_bytes_owned`](Self::alloc_bytes_owned).
  #[inline]
  pub fn alloc_bytes(&self, size: u32) -> Result<BytesRefMut, Error> {
    self.alloc_bytes_in(size).map(|a| match a {
      None => BytesRefMut::null(self),
      Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
    })
  }

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
  #[inline]
  pub fn alloc_aligned_bytes_owned<T>(&self, size: u32) -> Result<BytesMut, Error> {
    self
      .alloc_aligned_bytes::<T>(size)
      .map(|mut b| b.to_owned())
  }

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
  #[inline]
  pub fn alloc_aligned_bytes<T>(&self, size: u32) -> Result<BytesRefMut, Error> {
    self.alloc_aligned_bytes_in::<T>(size).map(|a| match a {
      None => BytesRefMut::null(self),
      Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
    })
  }

  /// Allocates a `T` in the ARENA.
  ///
  /// # Safety
  ///
  /// - If `T` needs to be dropped and callers invoke [`RefMut::detach`],
  ///   then the caller must ensure that the `T` is dropped before the ARENA is dropped.
  ///   Otherwise, it will lead to memory leaks.
  ///
  /// - If this is file backed ARENA, then `T` must be recoverable from bytes.
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
  /// // Do not invoke detach, so when the data is dropped, the drop logic will be handled by the ARENA.
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
  /// ### Recoverable type with file backed ARENA
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
  ///
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
  #[inline]
  pub unsafe fn alloc<T>(&self) -> Result<RefMut<'_, T>, Error> {
    if mem::size_of::<T>() == 0 {
      return Ok(RefMut::new_zst(self));
    }

    let allocated = self
      .alloc_in::<T>()?
      .expect("allocated size is not zero, but get None");
    let ptr = unsafe { self.get_aligned_pointer_mut::<T>(allocated.memory_offset as usize) };
    if mem::needs_drop::<T>() {
      unsafe {
        let ptr: *mut MaybeUninit<T> = ptr.as_ptr().cast();
        ptr::write(ptr, MaybeUninit::uninit());

        Ok(RefMut::new(ptr::read(ptr), allocated, self))
      }
    } else {
      Ok(RefMut::new_inline(ptr, allocated, self))
    }
  }

  /// Allocates a `T` in the ARENA. Like [`alloc`](Self::alloc), but returns an `Owned`.
  ///
  /// The cost is one more atomic operation than [`alloc`](Self::alloc).
  ///
  /// # Safety
  ///
  /// - See [`alloc`](Self::alloc) for safety.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{Arena, ArenaOptions};
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
  #[inline]
  pub unsafe fn alloc_owned<T>(&self) -> Result<Owned<T>, Error> {
    self.alloc::<T>().map(|mut r| r.to_owned())
  }

  /// Clear the ARENA.
  ///
  /// # Safety
  /// - The current pointers get from the ARENA cannot be used anymore after calling this method.
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
  /// use rarena_allocator::{Arena, ArenaOptions};
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
  pub unsafe fn clear(&self) -> Result<(), Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let memory = &mut *self.inner.as_ptr();
    memory.clear();

    Ok(())
  }

  /// Deallocates the memory at the given offset and size, the `offset..offset + size` will be made to a segment,
  /// returns `true` if the deallocation is successful.
  ///
  /// # Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  /// - `size` must be less than the capacity of the ARENA.
  /// - `offset + size` must be less than the capacity of the ARENA.
  pub unsafe fn dealloc(&self, offset: u32, size: u32) -> bool {
    // check if we have enough space to allocate a new segment in this segment.
    if !self.validate_segment(offset, size) {
      self.discard(size);
      return false;
    }

    let backoff = Backoff::new();

    unsafe {
      let header = self.header();

      loop {
        let (prev, next) = self.find_free_list_position(size);
        let prev_node = prev
          .map(|p| self.get_segment_node(p))
          .unwrap_or(&header.sentinel);
        let next_node_offset = next.unwrap_or(SENTINEL_SEGMENT_NODE_SIZE);

        self.write_segment_node(next_node_offset, offset, size);

        // CAS prev_node's next points to the new_node
        let prev_node_val = prev_node.load(Ordering::Acquire);
        let (_prev_node_offset, prev_node_size) = decode_segment_node(prev_node_val);

        // the prev is removed from the list, then we need to refind the position.
        if prev_node_size == 0 {
          // wait other thread to make progress.
          backoff.snooze();
          continue;
        }

        match prev_node.compare_exchange(
          prev_node_val,
          encode_segment_node(offset, size),
          Ordering::AcqRel,
          Ordering::Relaxed,
        ) {
          Ok(_) => {
            #[cfg(feature = "tracing")]
            tracing::debug!("dealloc {size} bytes at offset {offset}, prev segment: {_prev_node_offset}, next segment {next_node_offset}");
            break true;
          }
          Err(current_prev) => {
            let (_, size) = decode_segment_node(current_prev);
            // the prev is removed from the list, then we need to refind the position.
            if size == 0 {
              // wait other thread to make progress.
              backoff.snooze();
              continue;
            }

            backoff.spin();
          }
        }
      }
    }
  }

  /// Returns a bytes slice from the ARENA.
  ///
  /// # Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  /// - `size` must be less than the capacity of the ARENA.
  /// - `offset + size` must be less than the capacity of the ARENA.
  #[inline]
  pub const unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
    if offset == 0 {
      return &[];
    }

    let ptr = self.get_pointer(offset);
    slice::from_raw_parts(ptr, size)
  }

  /// Returns a mutable bytes slice from the ARENA.
  /// If the ARENA is read-only, then this method will return an empty slice.
  ///
  /// # Safety
  /// - `offset..offset + size` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  /// - `size` must be less than the capacity of the ARENA.
  /// - `offset + size` must be less than the capacity of the ARENA.
  ///
  /// # Panic
  /// - If the ARENA is read-only, then this method will panic.
  #[allow(clippy::mut_from_ref)]
  #[inline]
  pub unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8] {
    assert!(!self.ro, "ARENA is read-only");

    if offset == 0 {
      return &mut [];
    }

    let ptr = self.get_pointer_mut(offset);
    if ptr.is_null() {
      return &mut [];
    }

    slice::from_raw_parts_mut(ptr, size)
  }

  /// Returns a pointer to the memory at the given offset.
  ///
  /// # Safety
  /// - `offset` must be less than the capacity of the ARENA.
  #[inline]
  pub const unsafe fn get_pointer(&self, offset: usize) -> *const u8 {
    if offset == 0 {
      return self.ptr;
    }
    self.ptr.add(offset)
  }

  /// Returns a pointer to the memory at the given offset.
  /// If the ARENA is read-only, then this method will return a null pointer.
  ///
  /// # Safety
  /// - `offset` must be less than the capacity of the ARENA.
  ///
  /// # Panic
  /// - If the ARENA is read-only, then this method will panic.
  #[inline]
  pub unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8 {
    assert!(!self.ro, "ARENA is read-only");

    if offset == 0 {
      return self.ptr;
    }

    self.ptr.add(offset)
  }

  /// Returns an aligned pointer to the memory at the given offset.
  ///
  /// # Safety
  /// - `offset..offset + mem::size_of::<T>() + padding` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  #[inline]
  pub unsafe fn get_aligned_pointer<T>(&self, offset: usize) -> *const T {
    if offset == 0 {
      return ptr::null();
    }

    let align_offset = align_offset::<T>(offset as u32) as usize;
    self.ptr.add(align_offset).cast()
  }

  /// Returns an aligned pointer to the memory at the given offset.
  /// If the ARENA is read-only, then this method will return a null pointer.
  ///
  /// # Safety
  /// - `offset..offset + mem::size_of::<T>() + padding` must be allocated memory.
  /// - `offset` must be less than the capacity of the ARENA.
  ///
  /// # Panic
  /// - If the ARENA is read-only, then this method will panic.
  #[inline]
  pub unsafe fn get_aligned_pointer_mut<T>(&self, offset: usize) -> NonNull<T> {
    assert!(!self.ro, "ARENA is read-only");

    if offset == 0 {
      return NonNull::dangling();
    }

    let align_offset = align_offset::<T>(offset as u32) as usize;
    let ptr = self.ptr.add(align_offset).cast();
    NonNull::new_unchecked(ptr)
  }

  /// Returns the offset to the start of the ARENA.
  ///
  /// # Safety
  /// - `ptr` must be allocated by this ARENA.
  #[inline]
  pub unsafe fn offset(&self, ptr: *const u8) -> usize {
    let offset = ptr.offset_from(self.ptr);
    offset as usize
  }

  fn alloc_bytes_in(&self, size: u32) -> Result<Option<Allocated>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if size == 0 {
      return Ok(None);
    }

    let header = self.header();
    let mut allocated = header.allocated.load(Ordering::Acquire);

    loop {
      let want = allocated + size;
      if want > self.cap {
        break;
      }

      match header.allocated.compare_exchange_weak(
        allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(offset) => {
          #[cfg(feature = "tracing")]
          tracing::debug!("allocate {} bytes at offset {} from memory", size, offset);

          let allocated = Allocated::new(offset, size);
          unsafe { allocated.clear(self) };
          return Ok(Some(allocated));
        }
        Err(x) => allocated = x,
      }
    }

    // allocate through slow path
    let mut i = 0;

    loop {
      match self.alloc_slow_path(size) {
        Ok(bytes) => return Ok(Some(bytes)),
        Err(e) => {
          if i == self.max_retries - 1 {
            return Err(e);
          }
        }
      }
      i += 1;
    }
  }

  /// It is like a pop operation, we will always allocate from the largest segment.
  fn alloc_slow_path(&self, size: u32) -> Result<Allocated, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let backoff = Backoff::new();
    let header = self.header();

    loop {
      let head = header.sentinel.load(Ordering::Acquire);
      let (next, node_size) = decode_segment_node(head);
      // free list is empty
      if next == SENTINEL_SEGMENT_NODE_OFFSET && node_size == SENTINEL_SEGMENT_NODE_SIZE {
        return Err(Error::InsufficientSpace {
          requested: size,
          available: self.remaining() as u32,
        });
      }

      if node_size == REMOVED_SEGMENT_NODE_SIZE {
        // The current head is removed from the list, wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // The larget segment does not have enough space to allocate, so just return err.
      if size > node_size {
        return Err(Error::InsufficientSpace {
          requested: size,
          available: node_size,
        });
      }


      // CAS to remove the current
      let removed_head = encode_segment_node(next, REMOVED_SEGMENT_NODE_SIZE);
      if header
        .sentinel
        .compare_exchange(head, removed_head, Ordering::AcqRel, Ordering::Relaxed)
        .is_err()
      {
        // wait other thread to make progress.
        backoff.snooze();
        continue;
      }

      // We have successfully mark the head is removed, then we need to let head node's next point to the next node.

      // if we reach the end of the list, which means no next node.
      let next_node_val = if next != SENTINEL_SEGMENT_NODE_OFFSET {
        unsafe { self.get_segment_node(next).load(Ordering::Acquire) }
      } else {
        encode_segment_node(SENTINEL_SEGMENT_NODE_OFFSET, SENTINEL_SEGMENT_NODE_SIZE)
      };

      match header.sentinel.compare_exchange(
        removed_head,
        next_node_val,
        Ordering::AcqRel,
        Ordering::Relaxed,
      ) {
        Ok(_) => {
          // We have successfully remove the head node from the list.
          // Then we can allocate the memory.
          // give back the remaining memory to the free list.

          // Safety: the `next + size` is in bounds, and `node_size - size` is also in bounds.
          unsafe {
            self.dealloc(next + size, node_size - size);
          }

          #[cfg(feature = "tracing")]
          tracing::debug!("allocate {} bytes at offset {} from segment", size, next);
          let allocated = Allocated::new(next, size);
          unsafe { allocated.clear(self) };
          return Ok(allocated);
        }
        Err(current_sentinel) => {
          let (_, size) = decode_segment_node(current_sentinel);
          if size == 0 {
            // The current head is removed from the list, wait other thread to make progress.
            backoff.snooze();
            continue;
          }

          backoff.spin();
        }
      }
    }
  }

  fn alloc_aligned_bytes_in<T>(&self, extra: u32) -> Result<Option<Allocated>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if mem::size_of::<T>() == 0 {
      return self.alloc_bytes_in(extra);
    }

    let header = self.header();
    let mut allocated = header.allocated.load(Ordering::Acquire);

    loop {
      let aligned_offset = align_offset::<T>(allocated);
      let size = mem::size_of::<T>() as u32;
      let want = aligned_offset + size + extra;
      if want > self.cap {
        break;
      }

      match header.allocated.compare_exchange_weak(
        allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(offset) => {
          let mut allocated = Allocated::new(offset, want - offset);
          allocated.align_bytes_to::<T>();
          #[cfg(feature = "tracing")]
          tracing::debug!(
            "allocate {} bytes at offset {} from memory",
            want - offset,
            offset
          );
          return Ok(Some(allocated));
        }
        Err(x) => allocated = x,
      }
    }

    // allocate through slow path
    let mut i = 0;
    loop {
      match self.alloc_slow_path(Self::pad::<T>() as u32 + extra) {
        Ok(mut bytes) => {
          bytes.align_bytes_to::<T>();
          return Ok(Some(bytes));
        }
        Err(e) => {
          if i == self.max_retries - 1 {
            return Err(e);
          }
        }
      }
      i += 1;
    }
  }

  fn alloc_in<T>(&self) -> Result<Option<Allocated>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if mem::size_of::<T>() == 0 {
      return Ok(None);
    }

    let header = self.header();
    let mut allocated = header.allocated.load(Ordering::Acquire);
    loop {
      let align_offset = align_offset::<T>(allocated);
      let size = mem::size_of::<T>() as u32;
      let want = align_offset + size;
      if want > self.cap {
        break;
      }

      match header.allocated.compare_exchange_weak(
        allocated,
        want,
        Ordering::SeqCst,
        Ordering::Acquire,
      ) {
        Ok(offset) => {
          let mut allocated = Allocated::new(offset, want - offset);
          allocated.align_to::<T>();

          #[cfg(feature = "tracing")]
          tracing::debug!(
            "allocate {} bytes at offset {} from memory",
            want - offset,
            offset
          );
          
          unsafe { allocated.clear(self) };
          return Ok(Some(allocated));
        }
        Err(x) => allocated = x,
      }
    }

    // allocate through slow path
    let mut i = 0;
    loop {
      match self.alloc_slow_path(Self::pad::<T>() as u32) {
        Ok(mut allocated) => {
          allocated.align_to::<T>();
          return Ok(Some(allocated));
        }
        Err(e) => {
          if i == self.max_retries - 1 {
            return Err(e);
          }
        }
      }
      i += 1;
    }
  }

  /// Returns `true` if this offset and size is valid for a segment node.
  #[inline]
  fn validate_segment(&self, offset: u32, size: u32) -> bool {
    let aligned_offset = align_offset::<AtomicU64>(offset) as usize;
    let want = (aligned_offset - offset as usize) + mem::size_of::<AtomicU64>();
    if want >= size as usize {
      return false;
    }

    if size < self.header().min_segment_size.load(Ordering::Acquire) {
      return false;
    }

    true
  }

  fn find_free_list_position(&self, val: u32) -> (Option<u32>, Option<u32>) {
    let header = self.header();
    let mut current = &header.sentinel;

    let mut prev = 0;
    let backoff = Backoff::new();
    loop {
      let current_node = current.load(Ordering::Acquire);
      let (current_next, current_node_size) = decode_segment_node(current_node);

      // we reach the tail of the list
      if current_next == SENTINEL_SEGMENT_NODE_OFFSET {
        // the list is empty
        if prev == 0 {
          return (None, None);
        }

        return (Some(prev), None);
      }

      // the current is marked as removed
      if current_node_size == 0 {
        // wait other thread to remove the node.
        backoff.snooze();
        continue;
      }

      // the size is smaller than or equal to the val
      // then the value should be inserted before the current node
      if val >= current_node_size {
        if prev == 0 {
          return (None, Some(current_next));
        }

        return (Some(prev), Some(current_next));
      }

      let next = unsafe { self.get_segment_node(current_next) };

      prev = current_next;
      current = next;
      backoff.spin();
    }
  }

  #[inline]
  fn discard(&self, size: u32) {
    let header = self.header();

    #[cfg(feature = "tracing")]
    tracing::debug!("discard {size} bytes");

    header.discarded.fetch_add(size, Ordering::Release);
  }

  unsafe fn get_segment_node(&self, offset: u32) -> &AtomicU64 {
    let aligned_offset = align_offset::<AtomicU64>(offset);
    let ptr = self.ptr.add(aligned_offset as usize);
    &*(ptr as *const _)
  }

  unsafe fn write_segment_node(&self, next: u32, offset: u32, size: u32) -> u32 {
    let aligned_offset = align_offset::<AtomicU64>(offset);
    let node_ptr = self.ptr.add(aligned_offset as usize).cast::<AtomicU64>();
    (*node_ptr).store(encode_segment_node(next, size), Ordering::Release);
    offset
  }

  #[inline]
  fn new_in(memory: Memory, max_retries: u8, unify: bool, ro: bool) -> Self {
    let ptr = memory.as_mut_ptr();

    Self {
      cap: memory.cap(),
      unify,
      magic_version: memory.magic_version,
      version: memory.version,
      ptr,
      ro,
      max_retries,
      data_offset: memory.data_offset as u32,
      inner: unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(memory)) as _) },
    }
  }

  #[inline]
  fn pad<T>() -> usize {
    let size = mem::size_of::<T>();
    let align = mem::align_of::<T>();
    size + align - 1
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe {
      let memory_ptr = self.inner.as_ptr();
      let memory = &*memory_ptr;
      // `Memory` storage... follow the drop steps from Arc.
      if memory.refs.fetch_sub(1, Ordering::Release) != 1 {
        return;
      }

      // This fence is needed to prevent reordering of use of the data and
      // deletion of the data.  Because it is marked `Release`, the decreasing
      // of the reference count synchronizes with this `Acquire` fence. This
      // means that use of the data happens before decreasing the reference
      // count, which happens before this fence, which happens before the
      // deletion of the data.
      //
      // As explained in the [Boost documentation][1],
      //
      // > It is important to enforce any possible access to the object in one
      // > thread (through an existing reference) to *happen before* deleting
      // > the object in a different thread. This is achieved by a "release"
      // > operation after dropping a reference (any access to the object
      // > through this reference must obviously happened before), and an
      // > "acquire" operation before deleting the object.
      //
      // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
      //
      // Thread sanitizer does not support atomic fences. Use an atomic load
      // instead.
      memory.refs.load(Ordering::Acquire);
      // Drop the data
      let mut memory = Box::from_raw(memory_ptr);

      // Relaxed is enough here as we're in a drop, no one else can
      // access this memory anymore.
      memory.unmount();
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
fn bad_magic() -> std::io::Error {
  std::io::Error::new(std::io::ErrorKind::InvalidData, "arena has bad magic")
}

#[inline]
const fn decode_segment_node(val: u64) -> (u32, u32) {
  ((val >> 32) as u32, val as u32)
}

#[inline]
const fn encode_segment_node(next: u32, size: u32) -> u64 {
  ((next as u64) << 32) | size as u64
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
fn align_offset<T>(current_offset: u32) -> u32 {
  let alignment = mem::align_of::<T>() as u32;
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
    pub fn align_to<T>(&mut self) -> Result<NonNull<T>, BufferTooSmall> {
      if mem::size_of::<T>() == 0 {
        return Ok(NonNull::dangling());
      }

      let align_offset = super::align_offset::<T>(self.allocated.memory_offset + self.len as u32);

      if align_offset > self.allocated.memory_offset + self.allocated.memory_size {
        return Err(BufferTooSmall {
          remaining: self.allocated.memory_size as usize - self.len,
          want: align_offset as usize - self.len - self.allocated.memory_offset as usize,
        });
      }

      self.len = (align_offset - self.allocated.memory_offset) as usize;
      // SAFETY: We have checked the buffer size, and apply the align
      Ok(unsafe {
        NonNull::new_unchecked(self.as_mut_ptr().add(self.len).cast::<T>())
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
    ///   then the caller must ensure that the `T` is dropped before the ARENA is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed ARENA, then `T` must be recoverable from bytes.
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
    ///   then the caller must ensure that the `T` is dropped before the ARENA is dropped.
    ///   Otherwise, it will lead to memory leaks.
    ///
    /// - If this is file backed ARENA, then `T` must be recoverable from bytes.
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
}

mod bytes;
pub use bytes::*;

mod object;
pub use object::*;

#[cfg(test)]
mod tests;
