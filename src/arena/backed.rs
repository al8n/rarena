#[cfg(not(feature = "std"))]
use std::vec::Vec;

use super::*;

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

  #[inline]
  fn as_ptr(&self) -> *const u8 {
    self.ptr.as_ptr()
  }
}

enum SharedBackend {
  Vec(AlignedVec),
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  MmapMut {
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    lock: bool,
    data_ptr: *mut u8,
    shrink_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  Mmap {
    buf: *mut memmap2::Mmap,
    file: std::fs::File,
    lock: bool,
    data_ptr: *const u8,
    #[allow(dead_code)]
    shrink_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  AnonymousMmap {
    #[allow(dead_code)]
    buf: memmap2::MmapMut,
    data_ptr: *mut u8,
  },
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[derive(Debug)]
struct TooSmall {
  cap: usize,
  min_cap: usize,
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl TooSmall {
  #[inline]
  const fn new(cap: usize, min_cap: usize) -> Self {
    Self { cap, min_cap }
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl core::fmt::Display for TooSmall {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    write!(
      f,
      "memmap size is less than the minimum capacity: {} < {}",
      self.cap, self.min_cap
    )
  }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
impl std::error::Error for TooSmall {}

pub(super) struct Shared {
  pub(super) refs: AtomicUsize,
  cap: u32,
  pub(super) data_offset: usize,
  header_ptr: *mut u8,
  ptr: *mut u8,
  backend: SharedBackend,
}

impl Shared {
  pub(super) fn new_vec(cap: u32, alignment: usize, min_segment_size: u32) -> Self {
    let vec = AlignedVec::new(cap as usize, alignment);
    // Safety: we have add the overhead for the header
    unsafe {
      let ptr = vec.ptr.as_ptr();
      let header_ptr_offset = ptr.align_offset(mem::align_of::<Header>());
      let data_offset = header_ptr_offset + mem::size_of::<Header>();
      let this = Self {
        cap,
        refs: AtomicUsize::new(1),
        ptr,
        header_ptr: ptr.add(header_ptr_offset),
        backend: SharedBackend::Vec(vec),
        data_offset,
      };

      this
        .header_mut_ptr()
        .write(Header::new(data_offset as u32, min_segment_size));

      this
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    alignment: usize,
    min_segment_size: u32,
  ) -> std::io::Result<Self> {
    let (create_new, file) = open_options.open(path.as_ref())?;

    unsafe {
      mmap_options.map_mut(&file).and_then(|mut mmap| {
        let cap = mmap.len();
        if cap < OVERHEAD {
          return Err(invalid_data(TooSmall::new(cap, OVERHEAD)));
        }

        if create_new {
          // initialize the memory with 0
          ptr::write_bytes(mmap.as_mut_ptr(), 0, cap);
        }

        // TODO:  should we align the memory?
        let _alignment = alignment.max(mem::align_of::<Header>());

        let ptr = mmap.as_mut_ptr();
        let header_ptr_offset = ptr.align_offset(mem::align_of::<Header>());
        let data_offset = header_ptr_offset + mem::size_of::<Header>();

        let this = Self {
          cap: cap as u32,
          backend: SharedBackend::MmapMut {
            buf: Box::into_raw(Box::new(mmap)),
            file,
            lock: open_options.is_lock(),
            data_ptr: ptr.add(data_offset),
            shrink_on_drop: open_options.is_shrink_on_drop(),
          },
          header_ptr: ptr.add(header_ptr_offset) as _,
          ptr,
          refs: AtomicUsize::new(1),
          data_offset,
        };

        // Ensure that the header_ptr is correctly aligned
        if (this.header_ptr as usize) % mem::align_of::<Header>() != 0 {
          return Err(invalid_data(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Header pointer is not aligned",
          )));
        }

        // Safety: we have add the overhead for the header
        this
          .header_mut_ptr()
          .write(Header::new(data_offset as u32, min_segment_size));

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
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

        let ptr = mmap.as_ptr();
        let header_ptr_offset = ptr.align_offset(mem::align_of::<Header>());
        let data_offset = header_ptr_offset + mem::size_of::<Header>();

        let this = Self {
          cap: len as u32,
          backend: SharedBackend::Mmap {
            buf: Box::into_raw(Box::new(mmap)),
            file,
            lock: open_options.is_lock(),
            data_ptr: ptr.add(data_offset),
            shrink_on_drop: open_options.is_shrink_on_drop(),
          },
          header_ptr: ptr.add(header_ptr_offset) as _,
          ptr: ptr as _,
          refs: AtomicUsize::new(1),
          data_offset,
        };

        // Ensure that the header_ptr is correctly aligned
        if (this.header_ptr as usize) % mem::align_of::<Header>() != 0 {
          return Err(invalid_data(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Header pointer is not aligned",
          )));
        }

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn map_anon(
    mmap_options: MmapOptions,
    alignment: usize,
    min_segment_size: u32,
  ) -> std::io::Result<Self> {
    mmap_options.map_anon().and_then(|mut mmap| {
      if mmap.len() < OVERHEAD {
        return Err(invalid_data(TooSmall::new(mmap.len(), OVERHEAD)));
      }

      // TODO:  should we align the memory?
      let _alignment = alignment.max(mem::align_of::<Header>());
      let ptr = mmap.as_mut_ptr();
      let header_ptr_offset = ptr.align_offset(mem::align_of::<Header>());
      let data_offset = header_ptr_offset + mem::size_of::<Header>();

      // Safety: we have add the overhead for the header
      unsafe {
        let this = Self {
          cap: mmap.len() as u32,
          backend: SharedBackend::AnonymousMmap {
            buf: mmap,
            data_ptr: ptr.add(data_offset),
          },
          refs: AtomicUsize::new(1),
          data_offset,
          header_ptr: ptr.add(header_ptr_offset) as _,
          ptr,
        };

        // Ensure that the header_ptr is correctly aligned
        if (this.header_ptr as usize) % mem::align_of::<Header>() != 0 {
          return Err(invalid_data(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "Header pointer is not aligned",
          )));
        }

        this
          .header_mut_ptr()
          .write(Header::new(data_offset as u32, min_segment_size));
        Ok(this)
      }
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn flush(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush() },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(super) fn flush_async(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      SharedBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush_async() },
      _ => Ok(()),
    }
  }

  #[allow(dead_code)]
  #[inline]
  pub(super) const fn null(&self) -> *const u8 {
    self.ptr
  }

  #[inline]
  pub(super) const fn null_mut(&self) -> *mut u8 {
    self.ptr
  }

  #[inline]
  pub(super) fn as_mut_ptr(&mut self) -> Option<*mut u8> {
    unsafe {
      Some(match &mut self.backend {
        SharedBackend::Vec(vec) => vec.as_mut_ptr().add(self.data_offset),
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::MmapMut { data_ptr, .. } => *data_ptr,
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::Mmap { .. } => return None,
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::AnonymousMmap { data_ptr, .. } => *data_ptr,
      })
    }
  }

  #[inline]
  pub(super) fn as_ptr(&self) -> *const u8 {
    unsafe {
      match &self.backend {
        SharedBackend::Vec(vec) => vec.as_ptr().add(self.data_offset),
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::MmapMut { data_ptr, .. } => *data_ptr,
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::Mmap { data_ptr, .. } => *data_ptr,
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        SharedBackend::AnonymousMmap { data_ptr, .. } => *data_ptr,
      }
    }
  }

  #[inline]
  pub(super) const fn header_ptr(&self) -> *const u8 {
    self.header_ptr
  }

  #[inline]
  pub(super) const fn header_mut_ptr(&self) -> *mut Header {
    self.header_ptr as *mut Header
  }

  #[inline]
  pub(super) const fn cap(&self) -> u32 {
    self.cap
  }

  /// Only works on mmap with a file backend, unmounts the memory mapped file and truncates it to the specified size.
  ///
  /// ## Safety:
  /// - This method must be invoked in the drop impl of `Arena`.
  pub(super) unsafe fn unmount(&mut self) {
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    match &self.backend {
      SharedBackend::MmapMut {
        buf,
        file,
        lock,
        shrink_on_drop,
        ..
      } => {
        use fs4::FileExt;

        // we must trigger the drop of the mmap
        let used = if *shrink_on_drop {
          let header_ptr = self.header_ptr().cast::<Header>();
          let header = &*header_ptr;
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
      SharedBackend::Mmap {
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
          let header_ptr = self.header_ptr().cast::<Header>();
          let header = &*header_ptr;
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

#[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
mod tests {
  use super::*;

  #[test]
  fn test_too_small() {
    let too_small = TooSmall::new(10, 20);
    assert_eq!(
      std::format!("{}", too_small),
      "memmap size is less than the minimum capacity: 10 < 20"
    );
  }
}
