use core::{marker::PhantomData, ptr, slice};

use either::Either;

use super::{common::*, *};

pub(crate) trait PathRefCounter: Clone {
  #[cfg(feature = "std")]
  fn new(path: std::path::PathBuf) -> Self;

  #[cfg(feature = "std")]
  fn as_path(&self) -> &std::path::Path;
}

#[cfg(feature = "std")]
impl PathRefCounter for std::sync::Arc<std::path::PathBuf> {
  fn new(path: std::path::PathBuf) -> Self {
    std::sync::Arc::new(path)
  }

  fn as_path(&self) -> &std::path::Path {
    self
  }
}

#[cfg(not(feature = "std"))]
impl<T> PathRefCounter for std::sync::Arc<T> {}

#[cfg(feature = "std")]
impl PathRefCounter for std::rc::Rc<std::path::PathBuf> {
  fn new(path: std::path::PathBuf) -> Self {
    std::rc::Rc::new(path)
  }

  fn as_path(&self) -> &std::path::Path {
    self
  }
}

#[cfg(not(feature = "std"))]
impl<T> PathRefCounter for std::rc::Rc<T> {}

pub(crate) trait Header: Sized {
  fn new(size: u32, min_segment_size: u32) -> Self;

  fn load_min_segment_size(&self) -> u32;

  fn load_allocated(&self) -> u32;
}

enum MemoryBackend<P: PathRefCounter> {
  #[allow(dead_code)]
  Vec(AlignedVec, PhantomData<P>),
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  MmapMut {
    path: P,
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    remove_on_drop: AtomicBool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  Mmap {
    path: P,
    buf: *mut memmap2::Mmap,
    file: std::fs::File,
    remove_on_drop: AtomicBool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  AnonymousMmap {
    #[allow(dead_code)]
    buf: memmap2::MmapMut,
  },
}

pub(crate) trait RefCounter {
  fn new(val: usize) -> Self;

  fn fetch_add(&self, val: usize, ordering: Ordering) -> usize;

  fn fetch_sub(&self, val: usize, ordering: Ordering) -> usize;
}

impl RefCounter for AtomicUsize {
  fn new(val: usize) -> Self {
    AtomicUsize::new(val)
  }

  fn fetch_add(&self, val: usize, ordering: Ordering) -> usize {
    self.fetch_add(val, ordering)
  }

  fn fetch_sub(&self, val: usize, ordering: Ordering) -> usize {
    self.fetch_sub(val, ordering)
  }
}

impl RefCounter for UnsafeCell<usize> {
  fn new(val: usize) -> Self {
    UnsafeCell::new(val)
  }

  fn fetch_add(&self, value: usize, _ordering: Ordering) -> usize {
    let val = &mut *self.as_inner_ref_mut();
    let old = *val;
    *val += value;
    old
  }

  fn fetch_sub(&self, value: usize, _ordering: Ordering) -> usize {
    let val = &mut *self.as_inner_ref_mut();
    let old = *val;
    *val -= value;
    old
  }
}

pub(crate) struct Memory<R, P: PathRefCounter, H> {
  refs: R,
  reserved: usize,
  cap: u32,
  data_offset: usize,
  flag: MemoryFlags,
  header_ptr: Either<*mut u8, H>,
  ptr: *mut u8,
  #[allow(dead_code)]
  backend: MemoryBackend<P>,
  unify: bool,
  magic_version: u16,
  version: u16,
  freelist: Freelist,
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn mmap_mut(mmap_options: MmapOptions, file: &std::fs::File) -> std::io::Result<memmap2::MmapMut> {
  unsafe { mmap_options.map_mut(file) }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn mmap_copy(mmap_options: MmapOptions, file: &std::fs::File) -> std::io::Result<memmap2::MmapMut> {
  unsafe { mmap_options.map_copy(file) }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn mmap(mmap_options: MmapOptions, file: &std::fs::File) -> std::io::Result<memmap2::Mmap> {
  unsafe { mmap_options.map(file) }
}

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
#[inline]
fn mmap_copy_read_only(
  mmap_options: MmapOptions,
  file: &std::fs::File,
) -> std::io::Result<memmap2::Mmap> {
  unsafe { mmap_options.map_copy_read_only(file) }
}

impl<R: RefCounter, PR: PathRefCounter, H: Header> Memory<R, PR, H> {
  #[inline]
  pub(crate) const fn freelist(&self) -> Freelist {
    self.freelist
  }

  #[inline]
  pub(crate) const fn magic_version(&self) -> u16 {
    self.magic_version
  }

  #[inline]
  pub(crate) const fn version(&self) -> u16 {
    self.version
  }

  #[inline]
  pub(crate) const fn flag(&self) -> MemoryFlags {
    self.flag
  }

  #[inline]
  pub(crate) const fn data_offset(&self) -> usize {
    self.data_offset
  }

  #[inline]
  pub(crate) const fn reserved(&self) -> usize {
    self.reserved
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(crate) const fn path(&self) -> Option<&PR> {
    match &self.backend {
      MemoryBackend::MmapMut { path, .. } => Some(path),
      MemoryBackend::Mmap { path, .. } => Some(path),
      _ => None,
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  pub(crate) fn set_remove_on_drop(&self, val: bool) {
    match &self.backend {
      MemoryBackend::MmapMut { remove_on_drop, .. } => {
        remove_on_drop.store(val, Ordering::Release);
      }
      MemoryBackend::Mmap { remove_on_drop, .. } => {
        remove_on_drop.store(val, Ordering::Release);
      }
      _ => {}
    }
  }

  pub(crate) unsafe fn clear(&mut self) {
    let header_ptr_offset = align_offset::<H>(self.reserved as u32) as usize + mem::align_of::<H>();
    let data_offset = header_ptr_offset + mem::size_of::<H>();

    let min_segment_size = self.header().load_min_segment_size();
    let (header, data_offset) = if self.unify {
      let header_ptr = self.ptr.add(header_ptr_offset);
      let header = header_ptr.cast::<H>();
      header.write(H::new(data_offset as u32, min_segment_size));
      (Either::Left(header_ptr), data_offset)
    } else {
      (
        Either::Right(H::new(self.reserved as u32 + 1, min_segment_size)),
        self.reserved + 1,
      )
    };

    self.header_ptr = header;
    self.data_offset = data_offset;
  }

  pub(crate) fn new_vec(opts: ArenaOptions) -> Self {
    let cap = opts.capacity();
    let alignment = opts.maximum_alignment();
    let min_segment_size = opts.minimum_segment_size();
    let unify = opts.unify();

    let cap = if unify {
      cap.saturating_add(overhead::<H>() as u32)
    } else {
      cap.saturating_add(alignment as u32)
    } as usize;

    let mut vec = AlignedVec::new::<H>(cap, alignment);
    // Safety: we have add the overhead for the header
    unsafe {
      let ptr = vec.as_mut_ptr();
      ptr::write_bytes(ptr, 0, vec.cap);

      let reserved = opts.reserved() as usize;

      let header_ptr_offset = align_offset::<H>(opts.reserved()) as usize + mem::align_of::<H>();

      if reserved + header_ptr_offset + mem::size_of::<H>() > vec.cap {
        super::panic_reserved_too_large();
      }

      let mut data_offset = header_ptr_offset + mem::size_of::<H>();
      let header_ptr = ptr.add(header_ptr_offset).cast::<H>();

      let (header, data_offset) = if unify {
        super::write_sanity(
          opts.freelist() as u8,
          opts.magic_version(),
          slice::from_raw_parts_mut(ptr.add(reserved), 8),
        );
        header_ptr.write(H::new(data_offset as u32, min_segment_size));
        (Either::Left(header_ptr as _), data_offset)
      } else {
        data_offset = reserved + 1;
        (
          Either::Right(H::new((reserved + 1) as u32, min_segment_size)),
          data_offset,
        )
      };

      Self {
        cap: cap as u32,
        reserved: opts.reserved() as usize,
        refs: R::new(1),
        flag: MemoryFlags::empty(),
        ptr,
        header_ptr: header,
        backend: MemoryBackend::Vec(vec, PhantomData),
        data_offset,
        unify,
        magic_version: opts.magic_version(),
        version: CURRENT_VERSION,
        freelist: opts.freelist(),
      }
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::map_mut_in(
      path.as_ref().to_path_buf(),
      opts,
      open_options,
      mmap_options,
      mmap_mut,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_mut_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_mut_in(path, opts, open_options, mmap_options, mmap_mut).map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Self::map_mut_in(
      path.as_ref().to_path_buf(),
      opts,
      open_options,
      mmap_options,
      mmap_copy,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_mut_in(path, opts, open_options, mmap_options, mmap_copy).map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_mut_in(
    path: std::path::PathBuf,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    f: impl FnOnce(MmapOptions, &std::fs::File) -> std::io::Result<memmap2::MmapMut>,
  ) -> std::io::Result<Self> {
    let (create_new, file) = open_options.open(path.as_path())?;
    let file_size = file.metadata()?.len() as u32;
    let alignment = opts.maximum_alignment();
    let min_segment_size = opts.minimum_segment_size();
    let freelist = opts.freelist();
    let magic_version = opts.magic_version();
    let capacity = opts.capacity();

    let size = file_size.max(capacity);
    if size < overhead::<H>() as u32 {
      return Err(invalid_data(TooSmall::new(size as usize, overhead::<H>())));
    }

    if file_size < capacity {
      file.set_len(capacity as u64)?;
    }

    unsafe {
      f(mmap_options, &file).and_then(|mut mmap| {
        let cap = mmap.len();
        if cap < overhead::<H>() {
          return Err(invalid_data(TooSmall::new(cap, overhead::<H>())));
        }

        // TODO: should we align the memory?
        let _alignment = alignment.max(mem::align_of::<H>());

        let ptr = mmap.as_mut_ptr();

        let reserved = opts.reserved() as usize;

        let header_ptr_offset = align_offset::<H>(opts.reserved()) as usize + mem::align_of::<H>();

        if reserved + header_ptr_offset + mem::size_of::<H>() > capacity as usize {
          return Err(reserved_too_large());
        }

        let data_offset = header_ptr_offset + mem::size_of::<H>();
        let header_ptr = ptr.add(header_ptr_offset).cast::<H>();

        let (version, magic_version) = if create_new {
          // initialize the memory with 0
          ptr::write_bytes(ptr, 0, cap);

          super::write_sanity(
            freelist as u8,
            magic_version,
            slice::from_raw_parts_mut(ptr.add(reserved), mem::align_of::<H>()),
          );

          // Safety: we have add the overhead for the header
          header_ptr.write(Header::new(data_offset as u32, min_segment_size));

          (CURRENT_VERSION, magic_version)
        } else {
          let allocated = (*header_ptr).load_allocated();
          ptr::write_bytes(
            ptr.add(allocated as usize),
            0,
            mmap.len() - allocated as usize,
          );
          super::sanity_check(
            Some(freelist),
            magic_version,
            &mmap[reserved..reserved + mem::align_of::<H>()],
          )?;
          (CURRENT_VERSION, magic_version)
        };

        let this = Self {
          cap: cap as u32,
          reserved,
          flag: MemoryFlags::ON_DISK | MemoryFlags::MMAP,
          backend: MemoryBackend::MmapMut {
            remove_on_drop: AtomicBool::new(false),
            path: PR::new(path),
            buf: Box::into_raw(Box::new(mmap)),
            file,
          },
          header_ptr: Either::Left(header_ptr as _),
          ptr,
          refs: R::new(1),
          data_offset,
          unify: true,
          magic_version,
          version,
          freelist,
        };

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_with_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    reserved: u32,
    magic_version: u16,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_in(
      path,
      open_options,
      mmap_options,
      reserved,
      magic_version,
      mmap,
    )
    .map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    reserved: u32,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Self::map_in(
      path.as_ref().to_path_buf(),
      open_options,
      mmap_options,
      reserved,
      magic_version,
      mmap,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy_read_only_with_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    reserved: u32,
    magic_version: u16,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_in(
      path,
      open_options,
      mmap_options,
      reserved,
      magic_version,
      mmap_copy_read_only,
    )
    .map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy_read_only<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    reserved: u32,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Self::map_in(
      path.as_ref().to_path_buf(),
      open_options,
      mmap_options,
      reserved,
      magic_version,
      mmap_copy_read_only,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_in(
    path: std::path::PathBuf,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    reserved: u32,
    magic_version: u16,
    f: impl FnOnce(MmapOptions, &std::fs::File) -> std::io::Result<memmap2::Mmap>,
  ) -> std::io::Result<Self> {
    use either::Either;

    if !path.exists() {
      return Err(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "file not found",
      ));
    }

    let (_, file) = open_options.open(&path)?;

    unsafe {
      f(mmap_options, &file).and_then(|mmap| {
        let len = mmap.len();
        if len < overhead::<H>() {
          return Err(invalid_data(TooSmall::new(len, overhead::<H>())));
        }

        let reserved = reserved as usize;

        let ptr = mmap.as_ptr();
        let header_ptr_offset = align_offset::<H>(reserved as u32) as usize + mem::align_of::<H>();

        if reserved + header_ptr_offset + mem::size_of::<H>() > len {
          return Err(reserved_too_large());
        }

        let freelist = super::sanity_check(
          None,
          magic_version,
          &mmap[reserved..reserved + mem::align_of::<H>()],
        )?;
        let data_offset = header_ptr_offset + mem::size_of::<H>();
        let header_ptr = ptr.add(header_ptr_offset) as _;
        let this = Self {
          cap: len as u32,
          reserved,
          flag: MemoryFlags::ON_DISK | MemoryFlags::MMAP,
          backend: MemoryBackend::Mmap {
            remove_on_drop: AtomicBool::new(false),
            path: PR::new(path),
            buf: Box::into_raw(Box::new(mmap)),
            file,
          },
          header_ptr: Either::Left(header_ptr),
          ptr: ptr as _,
          refs: R::new(1),
          data_offset,
          unify: true,
          magic_version,
          version: CURRENT_VERSION,
          freelist,
        };

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_anon(
    mmap_options: MmapOptions,
    alignment: usize,
    min_segment_size: u32,
    unify: bool,
    reserved: u32,
    magic_version: u16,
    freelist: Freelist,
  ) -> std::io::Result<Self> {
    mmap_options.map_anon().and_then(|mut mmap| {
      if unify {
        if mmap.len() < overhead::<H>() {
          return Err(invalid_data(TooSmall::new(mmap.len(), overhead::<H>())));
        }
      } else if mmap.len() < alignment {
        return Err(invalid_data(TooSmall::new(mmap.len(), alignment)));
      }

      // TODO:  should we align the memory?
      let _alignment = alignment.max(mem::align_of::<H>());
      let ptr = mmap.as_mut_ptr();

      // Safety: we have add the overhead for the header
      unsafe {
        ptr::write_bytes(ptr, 0, mmap.len());

        let header_ptr_offset = align_offset::<H>(reserved) as usize + mem::align_of::<H>();
        let mut data_offset = header_ptr_offset + mem::size_of::<H>();
        let header_ptr = ptr.add(header_ptr_offset);

        if reserved as usize + header_ptr_offset + mem::size_of::<H>() > mmap.len() {
          return Err(reserved_too_large());
        }

        let (header, data_offset) = if unify {
          super::write_sanity(
            freelist as u8,
            magic_version,
            slice::from_raw_parts_mut(ptr.add(reserved as usize), mem::align_of::<H>()),
          );
          header_ptr
            .cast::<H>()
            .write(H::new(data_offset as u32, min_segment_size));
          (Either::Left(header_ptr as _), data_offset)
        } else {
          data_offset = reserved as usize + 1;
          (
            Either::Right(H::new(reserved + 1, min_segment_size)),
            data_offset,
          )
        };

        let this = Self {
          reserved: reserved as usize,
          flag: MemoryFlags::MMAP,
          cap: mmap.len() as u32,
          backend: MemoryBackend::AnonymousMmap { buf: mmap },
          refs: R::new(1),
          data_offset,
          header_ptr: header,
          ptr,
          unify,
          magic_version,
          version: CURRENT_VERSION,
          freelist,
        };

        Ok(this)
      }
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.lock_exclusive(),
      MemoryBackend::Mmap { file, .. } => file.lock_exclusive(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn lock_shared(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.lock_shared(),
      MemoryBackend::Mmap { file, .. } => file.lock_shared(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn try_lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.try_lock_exclusive(),
      MemoryBackend::Mmap { file, .. } => file.try_lock_exclusive(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn try_lock_shared(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.try_lock_shared(),
      MemoryBackend::Mmap { file, .. } => file.try_lock_shared(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn unlock(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.unlock(),
      MemoryBackend::Mmap { file, .. } => file.unlock(),
      _ => Ok(()),
    }
  }

  /// # Safety
  /// - offset and len must be valid and in bounds.
  #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
  pub(crate) unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    match &self.backend {
      MemoryBackend::MmapMut { buf, .. } => {
        let buf_len = (**buf).len();
        if offset + len > buf_len {
          return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "offset and len must be valid and in bounds",
          ));
        }

        let ptr = (**buf).as_ref().as_ptr().add(offset);
        rustix::mm::mlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      MemoryBackend::Mmap { buf, .. } => {
        let buf_len = (**buf).len();
        if offset + len > buf_len {
          return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "offset and len must be valid and in bounds",
          ));
        }

        let ptr = (**buf).as_ref().as_ptr();
        rustix::mm::mlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      _ => Ok(()),
    }
  }

  /// # Safety
  /// - offset and len must be valid and in bounds.
  #[cfg(all(feature = "memmap", not(target_family = "wasm"), not(windows)))]
  pub(crate) unsafe fn munlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    match &self.backend {
      MemoryBackend::MmapMut { buf, .. } => {
        let buf_len = (**buf).len();
        if offset + len > buf_len {
          return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "offset and len must be valid and in bounds",
          ));
        }

        let ptr = (**buf).as_ref().as_ptr().add(offset);
        rustix::mm::munlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      MemoryBackend::Mmap { buf, .. } => {
        let buf_len = (**buf).len();
        if offset + len > buf_len {
          return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "offset and len must be valid and in bounds",
          ));
        }

        let ptr = (**buf).as_ref().as_ptr();
        rustix::mm::munlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn flush(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush() },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn flush_async(&self) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush_async() },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn flush_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush_range(offset, len) },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe {
        (**mmap).flush_async_range(offset, len)
      },
      _ => Ok(()),
    }
  }

  #[allow(dead_code)]
  #[inline]
  pub(crate) const fn as_ptr(&self) -> *const u8 {
    self.ptr
  }

  #[inline]
  pub(crate) const fn as_mut_ptr(&self) -> *mut u8 {
    self.ptr
  }

  #[inline]
  pub(crate) fn header(&self) -> &H {
    unsafe {
      match &self.header_ptr {
        Either::Left(header_ptr) => &*(*header_ptr).cast::<H>(),
        Either::Right(header) => header,
      }
    }
  }

  #[inline]
  pub(crate) fn header_mut(&mut self) -> &mut H {
    unsafe {
      match &mut self.header_ptr {
        Either::Left(header_ptr) => &mut *(*header_ptr).cast::<H>(),
        Either::Right(header) => header,
      }
    }
  }

  #[inline]
  pub(crate) const fn cap(&self) -> u32 {
    self.cap
  }

  #[inline]
  pub(crate) const fn refs(&self) -> &R {
    &self.refs
  }

  /// Only works on mmap with a file backend, unmounts the memory mapped file and truncates it to the specified size.
  ///
  /// ## Safety:
  /// - This method must be invoked in the drop impl of `Arena`.
  pub(crate) unsafe fn unmount(&mut self) {
    // Any errors during unmapping/closing are ignored as the only way
    // to report them would be through panicking which is highly discouraged
    // in Drop impls, c.f. https://github.com/rust-lang/lang-team/issues/97

    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    match &mut self.backend {
      MemoryBackend::MmapMut {
        buf,
        file,
        path,
        remove_on_drop,
        ..
      } => {
        if remove_on_drop.load(Ordering::Acquire) {
          let _ = Box::from_raw(*buf);
          core::ptr::drop_in_place(file);
          let _ = std::fs::remove_file(path.as_path());
          return;
        }

        let _ = Box::from_raw(*buf);
        let _ = file.sync_all();
      }
      MemoryBackend::Mmap {
        path,
        file,
        buf,
        remove_on_drop,
        ..
      } => {
        if remove_on_drop.load(Ordering::Acquire) {
          let _ = Box::from_raw(*buf);
          core::ptr::drop_in_place(file);
          let _ = std::fs::remove_file(path.as_path());
          return;
        }

        let _ = Box::from_raw(*buf);
      }
      _ => {}
    }
  }
}

#[inline]
const fn overhead<H>() -> usize {
  mem::size_of::<H>()
}
