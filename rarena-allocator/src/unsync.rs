use core::{
  fmt,
  mem::{self, MaybeUninit},
  ptr::{self, NonNull},
  slice,
};

use either::Either;

use super::{common::*, sealed::Sealed, *};

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use crate::{MmapOptions, OpenOptions, PAGE_SIZE};

#[allow(unused_imports)]
use std::boxed::Box;

const OVERHEAD: usize = mem::size_of::<Header>();
const SEGMENT_NODE_SIZE: usize = mem::size_of::<SegmentNode>();

enum MemoryBackend {
  #[allow(dead_code)]
  Vec(AlignedVec),
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  MmapMut {
    path: std::rc::Rc<std::path::PathBuf>,
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    remove_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  Mmap {
    path: std::rc::Rc<std::path::PathBuf>,
    buf: *mut memmap2::Mmap,
    file: std::fs::File,
    remove_on_drop: bool,
  },
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  AnonymousMmap {
    #[allow(dead_code)]
    buf: memmap2::MmapMut,
  },
}

#[derive(Debug)]
#[repr(C, align(8))]
struct Header {
  /// The sentinel node for the ordered free list.
  sentinel: SegmentNode,
  allocated: u32,
  min_segment_size: u32,
  discarded: u32,
}

impl Header {
  #[inline]
  fn new(size: u32, min_segment_size: u32) -> Self {
    Self {
      allocated: size,
      sentinel: SegmentNode::sentinel(),
      min_segment_size,
      discarded: 0,
    }
  }
}

struct Memory {
  refs: usize,
  cap: u32,
  data_offset: usize,
  flag: MemoryFlags,
  header_ptr: Either<*mut u8, Header>,
  ptr: *mut u8,
  #[allow(dead_code)]
  backend: MemoryBackend,
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

impl Memory {
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  const fn path(&self) -> Option<&std::rc::Rc<std::path::PathBuf>> {
    match &self.backend {
      MemoryBackend::MmapMut { path, .. } => Some(path),
      MemoryBackend::Mmap { path, .. } => Some(path),
      _ => None,
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  fn set_remove_on_drop(&mut self, val: bool) {
    match &mut self.backend {
      MemoryBackend::MmapMut { remove_on_drop, .. } => {
        *remove_on_drop = val;
      }
      MemoryBackend::Mmap { remove_on_drop, .. } => {
        *remove_on_drop = val;
      }
      _ => {}
    }
  }

  unsafe fn clear(&mut self) {
    let header_ptr_offset = self.ptr.align_offset(mem::align_of::<Header>());
    let data_offset = header_ptr_offset + mem::size_of::<Header>();

    let min_segment_size = self.header().min_segment_size;
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

    let mut vec = AlignedVec::new::<Header>(cap, alignment);
    // Safety: we have add the overhead for the header
    unsafe {
      let ptr = vec.as_mut_ptr();
      ptr::write_bytes(ptr, 0, vec.cap);

      let header_ptr_offset = ptr.add(1).align_offset(mem::align_of::<Header>()) + 1;
      let mut data_offset = header_ptr_offset + mem::size_of::<Header>();
      let header_ptr = ptr.add(header_ptr_offset).cast::<Header>();

      let (header, data_offset) = if unify {
        Self::write_sanity(
          opts.freelist() as u8,
          opts.magic_version(),
          slice::from_raw_parts_mut(ptr, 8),
        );
        header_ptr.write(Header::new(data_offset as u32, min_segment_size));
        (Either::Left(header_ptr as _), data_offset)
      } else {
        data_offset = 1;
        (Either::Right(Header::new(1, min_segment_size)), data_offset)
      };

      Self {
        cap: cap as u32,
        refs: 1,
        flag: MemoryFlags::empty(),
        ptr,
        header_ptr: header,
        backend: MemoryBackend::Vec(vec),
        data_offset,
        unify,
        magic_version: opts.magic_version(),
        version: CURRENT_VERSION,
        freelist: opts.freelist(),
      }
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_mut<P: AsRef<std::path::Path>>(
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
  fn map_mut_with_path_builder<PB, E>(
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
  fn map_copy<P: AsRef<std::path::Path>>(
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
  fn map_copy_with_path_builder<PB, E>(
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
  fn map_mut_in(
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
    if size < OVERHEAD as u32 {
      return Err(invalid_data(TooSmall::new(size as usize, OVERHEAD)));
    }

    if file_size < capacity {
      file.set_len(capacity as u64)?;
    }

    unsafe {
      f(mmap_options, &file).and_then(|mut mmap| {
        let cap = mmap.len();
        if cap < OVERHEAD {
          return Err(invalid_data(TooSmall::new(cap, OVERHEAD)));
        }

        // TODO: should we align the memory?
        let _alignment = alignment.max(mem::align_of::<Header>());

        let ptr = mmap.as_mut_ptr();

        let header_ptr_offset = ptr.add(1).align_offset(mem::align_of::<Header>()) + 1;
        let data_offset = header_ptr_offset + mem::size_of::<Header>();
        let header_ptr = ptr.add(header_ptr_offset).cast::<Header>();

        let (version, magic_version) = if create_new {
          // initialize the memory with 0
          ptr::write_bytes(ptr, 0, cap);

          Self::write_sanity(
            freelist as u8,
            magic_version,
            slice::from_raw_parts_mut(ptr, header_ptr_offset),
          );

          // Safety: we have add the overhead for the header
          header_ptr.write(Header::new(data_offset as u32, min_segment_size));

          (CURRENT_VERSION, magic_version)
        } else {
          let allocated = (*header_ptr).allocated;
          ptr::write_bytes(
            ptr.add(allocated as usize),
            0,
            mmap.len() - allocated as usize,
          );
          Self::sanity_check(Some(freelist), magic_version, &mmap)?;
          (CURRENT_VERSION, magic_version)
        };

        let this = Self {
          cap: cap as u32,
          flag: MemoryFlags::ON_DISK | MemoryFlags::MMAP,
          backend: MemoryBackend::MmapMut {
            remove_on_drop: false,
            path: std::rc::Rc::new(path),
            buf: Box::into_raw(Box::new(mmap)),
            file,
          },
          header_ptr: Either::Left(header_ptr as _),
          ptr,
          refs: 1,
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
  fn map_with_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_in(path, open_options, mmap_options, magic_version, mmap).map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Self::map_in(
      path.as_ref().to_path_buf(),
      open_options,
      mmap_options,
      magic_version,
      mmap,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_copy_read_only_with_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
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
      magic_version,
      mmap_copy_read_only,
    )
    .map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_copy_read_only<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Self::map_in(
      path.as_ref().to_path_buf(),
      open_options,
      mmap_options,
      magic_version,
      mmap_copy_read_only,
    )
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn map_in(
    path: std::path::PathBuf,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
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
        if len < OVERHEAD {
          return Err(invalid_data(TooSmall::new(len, OVERHEAD)));
        }

        let freelist = Self::sanity_check(None, magic_version, &mmap)?;

        let ptr = mmap.as_ptr();
        let header_ptr_offset = ptr.add(1).align_offset(mem::align_of::<Header>()) + 1;
        let data_offset = header_ptr_offset + mem::size_of::<Header>();
        let header_ptr = ptr.add(header_ptr_offset) as _;
        let this = Self {
          cap: len as u32,
          flag: MemoryFlags::ON_DISK | MemoryFlags::MMAP,
          backend: MemoryBackend::Mmap {
            remove_on_drop: false,
            path: std::rc::Rc::new(path),
            buf: Box::into_raw(Box::new(mmap)),
            file,
          },
          header_ptr: Either::Left(header_ptr),
          ptr: ptr as _,
          refs: 1,
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
  fn map_anon(
    mmap_options: MmapOptions,
    alignment: usize,
    min_segment_size: u32,
    unify: bool,
    magic_version: u16,
    freelist: Freelist,
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
        let mut data_offset = header_ptr_offset + mem::size_of::<Header>();
        let header_ptr = ptr.add(header_ptr_offset);

        let (header, data_offset) = if unify {
          Self::write_sanity(
            freelist as u8,
            magic_version,
            slice::from_raw_parts_mut(ptr, header_ptr_offset),
          );
          header_ptr
            .cast::<Header>()
            .write(Header::new(data_offset as u32, min_segment_size));
          (Either::Left(header_ptr as _), data_offset)
        } else {
          data_offset = 1;
          (Either::Right(Header::new(1, min_segment_size)), data_offset)
        };

        let this = Self {
          flag: MemoryFlags::MMAP,
          cap: mmap.len() as u32,
          backend: MemoryBackend::AnonymousMmap { buf: mmap },
          refs: 1,
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
  fn lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.lock_exclusive(),
      MemoryBackend::Mmap { file, .. } => file.lock_exclusive(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn lock_shared(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.lock_shared(),
      MemoryBackend::Mmap { file, .. } => file.lock_shared(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn try_lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.try_lock_exclusive(),
      MemoryBackend::Mmap { file, .. } => file.try_lock_exclusive(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn try_lock_shared(&self) -> std::io::Result<()> {
    use fs4::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.try_lock_shared(),
      MemoryBackend::Mmap { file, .. } => file.try_lock_shared(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn unlock(&self) -> std::io::Result<()> {
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
  unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
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
  unsafe fn munlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
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

  #[inline]
  fn write_sanity(freelist: u8, magic_version: u16, data: &mut [u8]) {
    data[FREELIST_OFFSET] = freelist;
    data[MAGIC_TEXT_OFFSET..MAGIC_TEXT_OFFSET + MAGIC_TEXT_SIZE]
      .copy_from_slice(MAGIC_TEXT.as_ref());
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

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe { (**mmap).flush_range(offset, len) },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
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
  fn header_mut(&mut self) -> &mut Header {
    unsafe {
      match &mut self.header_ptr {
        Either::Left(header_ptr) => &mut *(*header_ptr).cast::<Header>(),
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
        if *remove_on_drop {
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
        if *remove_on_drop {
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

#[repr(transparent)]
struct SegmentNode {
  /// The first 32 bits are the size of the memory,
  /// the last 32 bits are the offset of the next segment node.
  size_and_next: UnsafeCell<u64>,
}

impl core::fmt::Debug for SegmentNode {
  fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
    let (offset, next) = decode_segment_node(*self.size_and_next.as_inner_ref());
    f.debug_struct("SegmentNode")
      .field("offset", &offset)
      .field("next", &next)
      .finish()
  }
}

impl core::ops::Deref for SegmentNode {
  type Target = UnsafeCell<u64>;

  #[inline]
  fn deref(&self) -> &Self::Target {
    &self.size_and_next
  }
}

impl SegmentNode {
  #[inline]
  fn sentinel() -> Self {
    Self {
      size_and_next: UnsafeCell::new(encode_segment_node(
        SENTINEL_SEGMENT_NODE_OFFSET,
        SENTINEL_SEGMENT_NODE_OFFSET,
      )),
    }
  }

  #[allow(clippy::mut_from_ref)]
  #[inline]
  fn as_inner_mut(&self) -> &mut u64 {
    unsafe { &mut *self.size_and_next.as_inner_mut() }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Segment {
  ptr: *mut u8,
  ptr_offset: u32,
  data_offset: u32,
  data_size: u32,
}

impl Segment {
  /// # Safety
  /// - offset must be a well-aligned and in-bounds `u64` pointer.
  #[inline]
  unsafe fn from_offset(arena: &Arena, offset: u32, data_size: u32) -> Self {
    Self {
      ptr: arena.ptr,
      ptr_offset: offset,
      data_offset: offset + SEGMENT_NODE_SIZE as u32,
      data_size,
    }
  }

  #[inline]
  fn as_mut(&mut self) -> &mut SegmentNode {
    // Safety: when constructing the Segment, we have checked the ptr_offset is in bounds and well-aligned.
    unsafe {
      let ptr = self.ptr.add(self.ptr_offset as usize);
      &mut *ptr.cast::<SegmentNode>()
    }
  }

  #[inline]
  fn update_next_node(&mut self, next: u32) {
    *self.as_mut().as_inner_mut() = encode_segment_node(self.data_size, next);
  }
}

/// Arena should be lock-free
pub struct Arena {
  ptr: *mut u8,
  data_offset: u32,
  flag: MemoryFlags,
  max_retries: u8,
  inner: NonNull<Memory>,
  unify: bool,
  magic_version: u16,
  version: u16,
  ro: bool,
  cap: u32,
  freelist: Freelist,
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  page_size: u32,
}

impl fmt::Debug for Arena {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let header = self.header();
    let allocated = header.allocated;

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
      let memory = &mut *self.inner.as_ptr();

      let refs = memory.refs;
      if refs > usize::MAX >> 1 {
        abort();
      }

      memory.refs += 1;

      // Safety:
      // The ptr is always non-null, and the data is only deallocated when the
      // last Arena is dropped.
      Self {
        max_retries: self.max_retries,
        flag: self.flag,
        magic_version: self.magic_version,
        version: self.version,
        ptr: self.ptr,
        data_offset: self.data_offset,
        ro: self.ro,
        inner: self.inner,
        unify: self.unify,
        cap: self.cap,
        freelist: self.freelist,
        #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
        page_size: self.page_size,
      }
    }
  }
}

impl Sealed for Arena {}

impl Allocator for Arena {
  fn raw_mut_ptr(&self) -> *mut u8 {
    self.ptr
  }

  fn raw_ptr(&self) -> *const u8 {
    self.ptr
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
  ///   field2: u32,
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
  /// assert_eq!(foo.field2, 20);
  /// ```
  #[inline]
  unsafe fn alloc<T>(&self) -> Result<RefMut<'_, T, Self>, Error> {
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
  fn alloc_aligned_bytes<T>(&self, size: u32) -> Result<BytesRefMut<Self>, Error> {
    self.alloc_aligned_bytes_in::<T>(size).map(|a| match a {
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
  fn alloc_aligned_bytes_owned<T>(&self, size: u32) -> Result<BytesMut<Self>, Error> {
    self
      .alloc_aligned_bytes::<T>(size)
      .map(|mut b| b.to_owned())
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
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn alloc_aligned_bytes_owned_within_page<T>(&self, size: u32) -> Result<BytesMut<Self>, Error> {
    self
      .alloc_aligned_bytes_within_page::<T>(size)
      .map(|mut b| b.to_owned())
  }

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
  /// let mut bytes = arena.alloc_aligned_bytes::<T>(extra).unwrap();
  /// bytes.put(val).unwrap(); // write `T` to the byte slice.
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn alloc_aligned_bytes_within_page<T>(&self, size: u32) -> Result<BytesRefMut<Self>, Error> {
    self
      .alloc_aligned_bytes_within_page_in::<T>(size)
      .map(|a| match a {
        None => BytesRefMut::null(self),
        Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
      })
  }

  /// Allocates a slice of memory in the ARENA.
  ///
  /// The [`BytesRefMut`] is zeroed out.
  ///
  /// If you want a [`BytesMut`], see [`alloc_bytes_owned`](Self::alloc_bytes_owned).
  #[inline]
  fn alloc_bytes(&self, size: u32) -> Result<BytesRefMut<Self>, Error> {
    self.alloc_bytes_in(size).map(|a| match a {
      None => BytesRefMut::null(self),
      Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
    })
  }

  /// Allocates an owned slice of memory in the ARENA.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes`](Self::alloc_bytes).
  #[inline]
  fn alloc_bytes_owned(&self, size: u32) -> Result<BytesMut<Self>, Error> {
    self.alloc_bytes(size).map(|mut b| b.to_owned())
  }

  /// Allocates an owned slice of memory in the ARENA in the same page.
  ///
  /// Compared to [`alloc_bytes_owned`](Self::alloc_bytes_owned), this method only allocates from the main memory, so
  /// the it means that if main memory does not have enough space but the freelist has segments can hold the size,
  /// this method will still return an error.
  ///
  /// The cost of this method is an extra atomic operation, compared to [`alloc_bytes_within_page`](Self::alloc_bytes_within_page).
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn alloc_bytes_owned_within_page(&self, size: u32) -> Result<BytesMut<Self>, Error> {
    self.alloc_bytes_within_page(size).map(|mut b| b.to_owned())
  }

  /// Allocates a slice of memory in the ARENA in the same page.
  ///
  /// Compared to [`alloc_bytes`](Self::alloc_bytes), this method only allocates from the main memory, so
  /// the it means that if main memory does not have enough space but the freelist has segments can hold the size,
  /// this method will still return an error.
  ///
  /// The [`BytesRefMut`] is zeroed out.
  ///
  /// If you want a [`BytesMut`], see [`alloc_bytes_owned_within_page`](Self::alloc_bytes_owned_within_page).
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn alloc_bytes_within_page(&self, size: u32) -> Result<BytesRefMut<Self>, Error> {
    self.alloc_bytes_within_page_in(size).map(|a| match a {
      None => BytesRefMut::null(self),
      Some(allocated) => unsafe { BytesRefMut::new(self, allocated) },
    })
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
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
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
  unsafe fn alloc_owned<T>(&self) -> Result<Owned<T, Self>, Error> {
    self.alloc::<T>().map(|mut r| r.to_owned())
  }

  /// Allocates a `T` in the ARENA in the same page. Like [`alloc_within_page`](Self::alloc_within_page), but returns an `Owned`.
  ///
  /// # Safety
  /// - See [`alloc`](Self::alloc) for safety.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  unsafe fn alloc_owned_within_page<T>(&self) -> Result<Owned<T, Self>, Error> {
    self.alloc_within_page::<T>().map(|mut r| r.to_owned())
  }

  /// Allocates a `T` in the ARENA in the same page.
  ///
  /// # Safety
  ///
  /// - See [`alloc`](Self::alloc) for safety.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  unsafe fn alloc_within_page<T>(&self) -> Result<RefMut<'_, T, Self>, Error> {
    if mem::size_of::<T>() == 0 {
      return Ok(RefMut::new_zst(self));
    }

    let allocated = self
      .alloc_within_page_in::<T>()?
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

  /// Returns the number of bytes allocated by the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let allocated = arena.allocated();
  /// ```
  #[inline]
  fn allocated(&self) -> usize {
    self.header().allocated as usize
  }

  /// Returns the whole main memory of the ARENA as a byte slice.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let memory = arena.memory();
  /// ```
  #[inline]
  fn allocated_memory(&self) -> &[u8] {
    let allocated = self.header().allocated;
    unsafe { slice::from_raw_parts(self.ptr, allocated as usize) }
  }

  /// Returns the capacity of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let capacity = arena.capacity();
  /// ```
  #[inline]
  fn capacity(&self) -> usize {
    self.cap as usize
  }

  /// Clear the ARENA.
  ///
  /// # Safety
  /// - The current pointers get from the ARENA cannot be used anymore after calling this method.
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
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
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
  unsafe fn clear(&self) -> Result<(), Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let memory = &mut *self.inner.as_ptr();
    memory.clear();

    Ok(())
  }

  /// Returns the data offset of the ARENA. The offset is the end of the reserved bytes of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let data_offset = arena.data_offset();
  /// ```
  #[inline]
  fn data_offset(&self) -> usize {
    self.data_offset as usize
  }

  /// Returns the data section of the ARENA as a byte slice, header is not included.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let data = arena.data();
  /// ```
  #[inline]
  fn data(&self) -> &[u8] {
    unsafe {
      let ptr = self.ptr.add(self.data_offset as usize);
      let allocated = self.header().allocated;
      slice::from_raw_parts(ptr, (allocated - self.data_offset) as usize)
    }
  }

  /// Deallocates the memory at the given offset and size, the `offset..offset + size` will be made to a segment,
  /// returns `true` if the deallocation is successful.
  ///
  /// # Safety
  /// - you must ensure the same `offset..offset + size` is not deallocated twice.
  /// - `offset` must be larger than the [`Arena::data_offset`].
  /// - `offset + size` must be less than the [`Arena::allocated`].
  #[inline]
  unsafe fn dealloc(&self, offset: u32, size: u32) -> bool {
    // first try to deallocate the memory back to the main memory.
    let header = self.header_mut();
    // if the offset + size is the current allocated size, then we can deallocate the memory back to the main memory.
    if header.allocated == offset + size {
      header.allocated = offset;
      return true;
    }

    match self.freelist {
      Freelist::None => {
        self.increase_discarded(size);
        true
      }
      Freelist::Optimistic => self.optimistic_dealloc(offset, size),
      Freelist::Pessimistic => self.pessimistic_dealloc(offset, size),
    }
  }

  /// Discards all freelist nodes in the ARENA.
  ///
  /// Returns the number of bytes discarded.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// arena.discard_freelist();
  /// ```
  #[inline]
  fn discard_freelist(&self) -> Result<u32, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    Ok(match self.freelist {
      Freelist::None => 0,
      _ => self.discard_freelist_in(),
    })
  }

  /// Returns the number of bytes discarded by the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let discarded = arena.discarded();
  /// ```
  #[inline]
  fn discarded(&self) -> u32 {
    self.header().discarded
  }

  /// Flushes the memory-mapped file to disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn flush(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().flush() }
  }

  /// Flushes the memory-mapped file to disk asynchronously.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn flush_async(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().flush_async() }
  }

  /// Flushes outstanding memory map modifications in the range to disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn flush_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    if len == 0 {
      return Ok(());
    }

    let page_size = (*PAGE_SIZE) as usize;

    // Calculate start page
    let start_page_offset = (offset / page_size) * page_size;

    // Calculate end page. The end offset is the last byte that needs to be flushed.
    let end_offset = offset + len - 1;
    let end_page_offset = ((end_offset / page_size) + 1) * page_size;

    // Check if the end of the last page exceeds the capacity of the memory map
    let end_flush_offset = end_page_offset.min(self.cap as usize);

    // Ensure that the flush does not start beyond the capacity
    if start_page_offset >= self.cap as usize {
      return Err(std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        "Offset is out of bounds",
      ));
    }

    unsafe {
      self
        .inner
        .as_ref()
        .flush_range(start_page_offset, end_flush_offset - start_page_offset)
    }
  }

  /// Asynchronously flushes outstanding memory map modifications in the range to disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    if len == 0 {
      return Ok(());
    }

    let page_size = (*PAGE_SIZE) as usize;

    // Calculate start page
    let start_page_offset = (offset / page_size) * page_size;

    // Calculate end page. The end offset is the last byte that needs to be flushed.
    let end_offset = offset + len - 1;
    let end_page_offset = ((end_offset / page_size) + 1) * page_size;

    // Check if the end of the last page exceeds the capacity of the memory map
    let end_flush_offset = end_page_offset.min(self.cap as usize);

    // Ensure that the flush does not start beyond the capacity
    if start_page_offset >= self.cap as usize {
      return Err(std::io::Error::new(
        std::io::ErrorKind::InvalidInput,
        "Offset is out of bounds",
      ));
    }

    unsafe {
      self
        .inner
        .as_ref()
        .flush_async_range(start_page_offset, end_flush_offset - start_page_offset)
    }
  }

  unsafe fn get_pointer(&self, offset: usize) -> *const u8 {
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
  ///
  #[allow(clippy::mut_from_ref)]
  #[inline]
  unsafe fn get_pointer_mut(&self, offset: usize) -> *mut u8 {
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
  unsafe fn get_aligned_pointer<T>(&self, offset: usize) -> *const T {
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
  unsafe fn get_aligned_pointer_mut<T>(&self, offset: usize) -> NonNull<T> {
    assert!(!self.ro, "ARENA is read-only");

    if offset == 0 {
      return NonNull::dangling();
    }

    let align_offset = align_offset::<T>(offset as u32) as usize;
    let ptr = self.ptr.add(align_offset).cast();
    NonNull::new_unchecked(ptr)
  }

  unsafe fn get_bytes(&self, offset: usize, size: usize) -> &[u8] {
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
  unsafe fn get_bytes_mut(&self, offset: usize, size: usize) -> &mut [u8] {
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

  /// Forcelly increases the discarded bytes.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// arena.increase_discarded(100);
  /// ```
  #[inline]
  fn increase_discarded(&self, size: u32) {
    #[cfg(feature = "tracing")]
    tracing::debug!("discard {size} bytes");

    self.header_mut().discarded += size;
  }

  /// Returns `true` if the ARENA is created through memory map.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let is_mmap = arena.is_mmap();
  /// assert_eq!(is_mmap, false);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn is_mmap(&self) -> bool {
    self.flag.contains(MemoryFlags::MMAP)
  }

  /// Returns `true` if the ARENA is on disk.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let is_ondisk = arena.is_ondisk();
  /// assert_eq!(is_ondisk, false);
  /// ```
  #[inline]
  fn is_ondisk(&self) -> bool {
    self.flag.contains(MemoryFlags::ON_DISK)
  }

  /// Returns `true` if the ARENA is on-disk and created through memory map.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let is_ondisk_and_mmap = arena.is_ondisk_and_mmap();
  /// assert_eq!(is_ondisk_and_mmap, false);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn is_ondisk_and_mmap(&self) -> bool {
    self
      .flag
      .contains(MemoryFlags::ON_DISK.union(MemoryFlags::MMAP))
  }

  /// Locks the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn lock_exclusive(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().lock_exclusive() }
  }

  /// Locks the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn lock_shared(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().lock_shared() }
  }

  /// Returns the magic version of the ARENA. This value can be used to check the compatibility for application using
  /// [`Arena`].
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let magic_version = arena.magic_version();
  /// ```
  #[inline]
  fn magic_version(&self) -> u16 {
    self.magic_version
  }

  /// Opens a read only ARENA backed by a mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  fn map<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Memory::map(path, open_options, mmap_options, magic_version)
      .map(|memory| Self::new_in(memory, 0, true, true))
  }

  /// Opens a read only ARENA backed by a mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  fn map_with_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    Memory::map_with_path_builder(path_builder, open_options, mmap_options, magic_version)
      .map(|memory| Self::new_in(memory, 0, true, true))
  }

  /// Creates a new ARENA backed by an anonymous mmap with the given capacity.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, MmapOptions};
  ///
  /// let mmap_options = MmapOptions::new().len(100);
  /// let arena = Arena::map_anon(ArenaOptions::new(), mmap_options).unwrap();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn map_anon(opts: ArenaOptions, mmap_options: MmapOptions) -> std::io::Result<Self> {
    Memory::map_anon(
      mmap_options,
      opts.maximum_alignment(),
      opts.minimum_segment_size(),
      opts.unify(),
      opts.magic_version(),
      opts.freelist(),
    )
    .map(|memory| Self::new_in(memory, opts.maximum_retries(), opts.unify(), false))
  }

  /// Creates a new ARENA backed by a copy-on-write memory map backed by a file.
  ///
  /// Data written to the ARENA will not be visible by other processes, and will not be carried through to the underlying file.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  fn map_copy<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Memory::map_copy(path, opts, open_options, mmap_options)
      .map(|memory| Self::new_in(memory, opts.maximum_retries(), true, false))
  }

  /// Creates a new ARENA backed by a copy-on-write memory map backed by a file with the given path builder.
  ///
  /// Data written to the ARENA will not be visible by other processes, and will not be carried through to the underlying file.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  fn map_copy_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    Memory::map_copy_with_path_builder(path_builder, opts, open_options, mmap_options)
      .map(|memory| Self::new_in(memory, opts.maximum_retries(), true, false))
  }

  /// Opens a read only ARENA backed by a copy-on-write read-only memory map backed by a file.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  /// let arena = Arena::map_copy_read_only(&path, open_options, mmap_options, 0).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn map_copy_read_only<P: AsRef<std::path::Path>>(
    path: P,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> std::io::Result<Self> {
    Memory::map_copy_read_only(path, open_options, mmap_options, magic_version)
      .map(|memory| Self::new_in(memory, 0, true, true))
  }

  /// Opens a read only ARENA backed by a copy-on-write read-only memory map backed by a file with the given path builder.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  /// let arena = Arena::map_copy_read_only_with_path_builder::<_, std::io::Error>(|| Ok(path.to_path_buf()), open_options, mmap_options, 0).unwrap();
  ///
  /// # std::fs::remove_file(path);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn map_copy_read_only_with_path_builder<PB, E>(
    path_builder: PB,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
    magic_version: u16,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    Memory::map_copy_read_only_with_path_builder(
      path_builder,
      open_options,
      mmap_options,
      magic_version,
    )
    .map(|memory| Self::new_in(memory, 0, true, true))
  }

  /// Creates a new ARENA backed by a mmap with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> std::io::Result<Self> {
    Memory::map_mut(path, opts, open_options, mmap_options)
      .map(|memory| Self::new_in(memory, opts.maximum_retries(), true, false))
  }

  /// Creates a new ARENA backed by a mmap with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  fn map_mut_with_path_builder<PB, E>(
    path_builder: PB,
    opts: ArenaOptions,
    open_options: OpenOptions,
    mmap_options: MmapOptions,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    Memory::map_mut_with_path_builder(path_builder, opts, open_options, mmap_options)
      .map(|memory| Self::new_in(memory, opts.maximum_retries(), true, false))
  }

  /// Returns the whole main memory of the ARENA as a byte slice.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let memory = arena.memory();
  /// ```
  #[inline]
  fn memory(&self) -> &[u8] {
    unsafe { slice::from_raw_parts(self.ptr, self.cap as usize) }
  }

  /// Returns the minimum segment size of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let min_segment_size = arena.minimum_segment_size();
  /// ```
  #[inline]
  fn minimum_segment_size(&self) -> u32 {
    self.header().min_segment_size
  }

  /// Sets the minimum segment size of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let mut arena = Arena::new(ArenaOptions::new());
  /// arena.set_minimum_segment_size(100);
  /// ```
  #[inline]
  fn set_minimum_segment_size(&self, size: u32) {
    self.header_mut().min_segment_size = size;
  }

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
  #[inline]
  unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().mlock(offset, len) }
  }

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
  #[inline]
  unsafe fn munlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().munlock(offset, len) }
  }

  /// Creates a new ARENA with the given options.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// ```
  #[inline]
  fn new(opts: ArenaOptions) -> Self {
    let memory = Memory::new_vec(opts);
    Self::new_in(memory, opts.maximum_retries(), opts.unify(), false)
  }

  /// Returns the offset to the start of the ARENA.
  ///
  /// # Safety
  /// - `ptr` must be allocated by this ARENA.
  #[inline]
  unsafe fn offset(&self, ptr: *const u8) -> usize {
    let offset = ptr.offset_from(self.ptr);
    offset as usize
  }

  /// Returns the page size.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let page_size = arena.page_size();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn page_size(&self) -> usize {
    self.page_size as usize
  }

  /// Returns `true` if the arena is read-only.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let read_only = arena.read_only();
  /// ```
  #[inline]
  fn read_only(&self) -> bool {
    self.ro
  }

  /// Returns the number of references to the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let refs = arena.refs();
  /// ```
  #[inline]
  fn refs(&self) -> usize {
    unsafe { self.inner.as_ref().refs }
  }

  /// Returns the number of bytes remaining bytes can be allocated by the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let remaining = arena.remaining();
  /// ```
  #[inline]
  fn remaining(&self) -> usize {
    (self.cap as usize).saturating_sub(self.allocated())
  }

  /// Sets remove on drop, only works on mmap with a file backend.
  ///
  /// Default is `false`.
  ///
  /// > **WARNING:** Once set to `true`, the backed file will be removed when the ARENA is dropped, even though the file is opened in
  /// > read-only mode.
  ///
  /// # Example
  ///
  /// ```rust
  /// # use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// # let mut arena = Arena::new(ArenaOptions::new());
  /// arena.remove_on_drop(true);
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  fn remove_on_drop(&self, remove_on_drop: bool) {
    // Safety: the inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { (*self.inner.as_ptr()).set_remove_on_drop(remove_on_drop) }
  }

  /// Set back the ARENA's main memory cursor to the given position.
  ///
  /// # Safety
  /// - If the current position is larger than the given position,
  ///   then the memory between the current position and the given position will be reclaimed,
  ///   so must ensure the memory chunk between the current position and the given position will not
  ///   be accessed anymore.
  unsafe fn rewind(&self, pos: ArenaPosition) {
    let data_offset = self.data_offset;
    let cap = self.cap;
    let header = self.header_mut();
    let allocated = header.allocated;
    let final_offset = match pos {
      ArenaPosition::Start(offset) => offset.max(data_offset).min(cap),
      ArenaPosition::Current(offset) => {
        let offset = allocated as i64 + offset;
        #[allow(clippy::comparison_chain)]
        if offset > 0 {
          if offset >= (cap as i64) {
            cap
          } else {
            let offset = offset as u32;
            offset.max(data_offset).min(cap)
          }
        } else if offset < 0 {
          data_offset
        } else {
          return;
        }
      }
      ArenaPosition::End(offset) => match cap.checked_sub(offset) {
        Some(val) => val.max(data_offset),
        None => data_offset,
      },
    };

    header.allocated = final_offset;
  }

  /// Try to lock the underlying file for exclusive access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn try_lock_exclusive(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().try_lock_exclusive() }
  }

  /// Try to lock the underlying file for shared access, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  fn try_lock_shared(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().try_lock_shared() }
  }

  /// Unlocks the underlying file, only works on mmap with a file backend.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions, OpenOptions, MmapOptions};
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
  #[inline]
  fn unlock(&self) -> std::io::Result<()> {
    unsafe { self.inner.as_ref().unlock() }
  }

  /// Returns the version of the ARENA.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// let arena = Arena::new(ArenaOptions::new());
  /// let version = arena.version();
  /// ```
  #[inline]
  fn version(&self) -> u16 {
    self.version
  }
}

impl Arena {
  /// Returns the path of the mmap file, only returns `Some` when the ARENA is backed by a mmap file.
  ///
  /// # Example
  ///
  /// ```rust
  /// # use rarena_allocator::{unsync::Arena, Allocator, ArenaOptions};
  ///
  /// # let arena = Arena::new(ArenaOptions::new());
  /// let path = arena.path();
  /// ```
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  #[inline]
  pub fn path(&self) -> Option<&std::rc::Rc<std::path::PathBuf>> {
    // Safety: the inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { self.inner.as_ref().path() }
  }

  #[inline]
  fn header(&self) -> &Header {
    // Safety:
    // The inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { (*self.inner.as_ptr()).header() }
  }

  #[allow(clippy::mut_from_ref)]
  #[inline]
  fn header_mut(&self) -> &mut Header {
    // Safety:
    // The inner is always non-null, we only deallocate it when the memory refs is 1.
    unsafe { (*self.inner.as_ptr()).header_mut() }
  }

  /// Returns the free list position to insert the value.
  /// - `None` means that we should insert to the head.
  /// - `Some(offset)` means that we should insert after the offset. offset -> new -> next
  fn find_position(&self, val: u32, check: impl Fn(u32, u32) -> bool) -> (u64, &UnsafeCell<u64>) {
    let header = self.header_mut();
    let mut current: &UnsafeCell<u64> = &header.sentinel;
    let mut current_node = current.as_inner_ref();
    let (mut current_node_size, mut next_offset) = decode_segment_node(*current_node);

    loop {
      // the list is empty
      if current_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && next_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return (*current_node, current);
      }

      // the current is marked as remove and the next is the tail.
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return (*current_node, current);
      }

      // the next is the tail, then we should insert the value after the current node.
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return (*current_node, current);
      }

      let next = self.get_segment_node(next_offset);
      let next_node = next.as_inner_ref();
      let (next_node_size, next_next_offset) = decode_segment_node(*next_node);

      if check(val, next_node_size) {
        return (*current_node, current);
      }

      current = next;
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  #[allow(clippy::type_complexity)]
  fn find_prev_and_next(
    &self,
    val: u32,
    check: impl Fn(u32, u32) -> bool,
  ) -> Option<((u64, &UnsafeCell<u64>), (u64, &UnsafeCell<u64>))> {
    let header = self.header();
    let mut current: &UnsafeCell<u64> = &header.sentinel;
    let mut current_node = current.as_inner_ref();
    let (mut current_node_size, mut next_offset) = decode_segment_node(*current_node);

    loop {
      // the list is empty
      if current_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && next_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return None;
      }

      // the current is marked as remove and the next is the tail.
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return None;
      }

      // the next is the tail
      if next_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        return None;
      }

      let next = self.get_segment_node(next_offset);
      let next_node = next.as_inner_ref();
      let (next_node_size, next_next_offset) = decode_segment_node(*next_node);

      if check(val, next_node_size) {
        return Some(((*current_node, current), (*next_node, next)));
      }

      current = self.get_segment_node(next_offset);
      current_node = next_node;
      current_node_size = next_node_size;
      next_offset = next_next_offset;
    }
  }

  fn optimistic_dealloc(&self, offset: u32, size: u32) -> bool {
    // check if we have enough space to allocate a new segment in this segment.
    let Some(mut segment_node) = self.try_new_segment(offset, size) else {
      return false;
    };

    loop {
      let (current_node_size_and_next_node_offset, current) = self
        .find_position(segment_node.data_size, |val, next_node_size| {
          val >= next_node_size
        });
      let (node_size, next_node_offset) =
        decode_segment_node(current_node_size_and_next_node_offset);

      if segment_node.ptr_offset == next_node_offset {
        continue;
      }

      segment_node.update_next_node(next_node_offset);

      *current.as_inner_ref_mut() = encode_segment_node(node_size, segment_node.ptr_offset);

      #[cfg(feature = "tracing")]
      tracing::debug!(
        "create segment node ({} bytes) at {}, next segment {next_node_offset}",
        segment_node.data_size,
        segment_node.ptr_offset
      );

      self.increase_discarded(segment_node.data_offset - segment_node.ptr_offset);
      return true;
    }
  }

  fn pessimistic_dealloc(&self, offset: u32, size: u32) -> bool {
    // check if we have enough space to allocate a new segment in this segment.
    let Some(mut segment_node) = self.try_new_segment(offset, size) else {
      return false;
    };

    let (current_node_size_and_next_node_offset, current) = self
      .find_position(segment_node.data_size, |val, next_node_size| {
        val <= next_node_size
      });
    let (node_size, next_node_offset) = decode_segment_node(current_node_size_and_next_node_offset);

    segment_node.update_next_node(next_node_offset);

    *current.as_inner_ref_mut() = encode_segment_node(node_size, segment_node.ptr_offset);

    #[cfg(feature = "tracing")]
    tracing::debug!(
      "create segment node ({} bytes) at {}, next segment {next_node_offset}",
      segment_node.data_size,
      segment_node.ptr_offset
    );

    self.increase_discarded(segment_node.data_offset - segment_node.ptr_offset);
    true
  }

  fn alloc_bytes_in(&self, size: u32) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if size == 0 {
      return Ok(None);
    }
    let header = self.header_mut();

    let want = header.allocated + size;
    if want <= self.cap {
      let offset = header.allocated;
      header.allocated = want;

      #[cfg(feature = "tracing")]
      tracing::debug!("allocate {} bytes at offset {} from memory", size, offset);

      let allocated = Meta::new(self.ptr as _, offset, size);
      unsafe { allocated.clear(self) };
      return Ok(Some(allocated));
    }

    // allocate through slow path
    match self.freelist {
      Freelist::None => Err(Error::InsufficientSpace {
        requested: size,
        available: self.remaining() as u32,
      }),
      Freelist::Optimistic => match self.alloc_slow_path_optimistic(size) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) => Err(e),
      },
      Freelist::Pessimistic => match self.alloc_slow_path_pessimistic(size) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) => Err(e),
      },
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn alloc_bytes_within_page_in(&self, size: u32) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if size == 0 {
      return Ok(None);
    }

    if size > self.page_size {
      return Err(Error::larger_than_page_size(size, self.page_size));
    }

    let header = self.header_mut();
    let mut padding_to_next_page = 0;

    let page_boundary = self.nearest_page_boundary(header.allocated);
    let mut want = header.allocated + size;

    // Ensure that the allocation will fit within page
    if want > page_boundary {
      // Adjust the allocation to start at the next page boundary
      padding_to_next_page = page_boundary - header.allocated;
      want += padding_to_next_page;
    }

    if want <= self.cap {
      let offset = header.allocated;
      header.allocated = want;

      #[cfg(feature = "tracing")]
      tracing::debug!(
        "allocate {} bytes at offset {} from memory",
        size + padding_to_next_page,
        offset
      );

      let mut allocated = Meta::new(self.ptr as _, offset, size + padding_to_next_page);
      allocated.ptr_offset = allocated.memory_offset + padding_to_next_page;
      allocated.ptr_size = size;
      unsafe { allocated.clear(self) };

      #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
      self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

      return Ok(Some(allocated));
    }

    Err(Error::InsufficientSpace {
      requested: want - header.allocated,
      available: self.remaining() as u32,
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  fn nearest_page_boundary(&self, offset: u32) -> u32 {
    // Calculate the nearest page boundary after the offset
    let remainder = offset % self.page_size;
    if remainder == 0 {
      offset // Already at a page boundary
    } else {
      offset + (self.page_size - remainder)
    }
  }

  fn alloc_aligned_bytes_in<T>(&self, extra: u32) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    if mem::size_of::<T>() == 0 {
      return self.alloc_bytes_in(extra);
    }

    let header = self.header_mut();
    let allocated = header.allocated;
    let aligned_offset = align_offset::<T>(allocated);
    let size = mem::size_of::<T>() as u32;
    let want = aligned_offset + size + extra;

    if want <= self.cap {
      // break size + extra;
      let offset = header.allocated;
      header.allocated = want;
      let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
      allocated.align_bytes_to::<T>();
      #[cfg(feature = "tracing")]
      tracing::debug!(
        "allocate {} bytes at offset {} from memory",
        want - offset,
        offset
      );
      return Ok(Some(allocated));
    }

    // allocate through slow path
    match self.freelist {
      Freelist::None => Err(Error::InsufficientSpace {
        requested: size + extra,
        available: self.remaining() as u32,
      }),
      Freelist::Optimistic => {
        match self.alloc_slow_path_optimistic(Self::pad::<T>() as u32 + extra) {
          Ok(mut bytes) => {
            bytes.align_bytes_to::<T>();
            Ok(Some(bytes))
          }
          Err(e) => Err(e),
        }
      }
      Freelist::Pessimistic => {
        match self.alloc_slow_path_pessimistic(Self::pad::<T>() as u32 + extra) {
          Ok(mut bytes) => {
            bytes.align_bytes_to::<T>();
            Ok(Some(bytes))
          }
          Err(e) => Err(e),
        }
      }
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn alloc_aligned_bytes_within_page_in<T>(&self, extra: u32) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let t_size = mem::size_of::<T>();

    if t_size == 0 {
      return self.alloc_bytes_within_page_in(extra);
    }

    let header = self.header_mut();
    let allocated = header.allocated;

    let page_boundary = self.nearest_page_boundary(allocated);
    let mut aligned_offset = align_offset::<T>(allocated);
    let size = t_size as u32;
    let mut want = aligned_offset + size + extra;
    let mut estimated_size = want - allocated;

    // Ensure that the allocation will fit within page
    if want > page_boundary {
      aligned_offset = align_offset::<T>(page_boundary);
      want = aligned_offset + size + extra;
      estimated_size = (aligned_offset - page_boundary) + size + extra;
    }

    if estimated_size > self.page_size {
      return Err(Error::larger_than_page_size(estimated_size, self.page_size));
    }

    if want <= self.cap {
      let offset = header.allocated;
      header.allocated = want;

      let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
      allocated.ptr_offset = aligned_offset;
      allocated.ptr_size = size + extra;
      unsafe { allocated.clear(self) };

      #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
      self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

      #[cfg(feature = "tracing")]
      tracing::debug!(
        "allocate {} bytes at offset {} from memory",
        want - offset,
        offset
      );
      return Ok(Some(allocated));
    }

    Err(Error::InsufficientSpace {
      requested: want,
      available: self.remaining() as u32,
    })
  }

  fn alloc_in<T>(&self) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let t_size = mem::size_of::<T>();
    if t_size == 0 {
      return Ok(None);
    }

    let header = self.header_mut();
    let allocated = header.allocated;
    let align_offset = align_offset::<T>(allocated);
    let size = t_size as u32;
    let want = align_offset + size;

    if want <= self.cap {
      let offset = header.allocated;
      header.allocated = want;
      let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
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

    // allocate through slow path
    match self.freelist {
      Freelist::None => Err(Error::InsufficientSpace {
        requested: want,
        available: self.remaining() as u32,
      }),
      Freelist::Optimistic => match self.alloc_slow_path_optimistic(Self::pad::<T>() as u32) {
        Ok(mut allocated) => {
          allocated.align_to::<T>();
          Ok(Some(allocated))
        }
        Err(e) => Err(e),
      },
      Freelist::Pessimistic => match self.alloc_slow_path_pessimistic(Self::pad::<T>() as u32) {
        Ok(mut allocated) => {
          allocated.align_to::<T>();
          Ok(Some(allocated))
        }
        Err(e) => Err(e),
      },
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  fn alloc_within_page_in<T>(&self) -> Result<Option<Meta>, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let t_size = mem::size_of::<T>();

    if t_size == 0 {
      return Ok(None);
    }

    if t_size as u32 > self.page_size {
      return Err(Error::larger_than_page_size(t_size as u32, self.page_size));
    }

    let header = self.header_mut();
    let allocated = header.allocated;
    let page_boundary = self.nearest_page_boundary(allocated);
    let mut aligned_offset = align_offset::<T>(allocated);
    let size = mem::size_of::<T>() as u32;
    let mut want = aligned_offset + size;
    let mut estimated_size = want - allocated;

    // Ensure that the allocation will fit within page
    if want > page_boundary {
      aligned_offset = align_offset::<T>(page_boundary);
      want = aligned_offset + size;
      estimated_size = (aligned_offset - page_boundary) + size;
    }

    if estimated_size > self.page_size {
      return Err(Error::larger_than_page_size(estimated_size, self.page_size));
    }

    if want <= self.cap {
      let offset = header.allocated;
      header.allocated = want;
      let mut allocated = Meta::new(self.ptr as _, offset, want - offset);
      allocated.ptr_offset = aligned_offset;
      allocated.ptr_size = size;
      unsafe { allocated.clear(self) };

      #[cfg(all(test, feature = "memmap", not(target_family = "wasm")))]
      self.check_page_boundary(allocated.ptr_offset, allocated.ptr_size);

      #[cfg(feature = "tracing")]
      tracing::debug!(
        "allocate {} bytes at offset {} from memory",
        want - offset,
        offset
      );

      unsafe { allocated.clear(self) };
      return Ok(Some(allocated));
    }

    Err(Error::InsufficientSpace {
      requested: want,
      available: self.remaining() as u32,
    })
  }

  fn alloc_slow_path_pessimistic(&self, size: u32) -> Result<Meta, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let Some(((prev_node_val, prev_node), (next_node_val, _))) =
      self.find_prev_and_next(size, |val, next_node_size| val <= next_node_size)
    else {
      return Err(Error::InsufficientSpace {
        requested: size,
        available: self.remaining() as u32,
      });
    };

    let (prev_node_size, next_node_offset) = decode_segment_node(prev_node_val);
    let (next_node_size, next_next_node_offset) = decode_segment_node(next_node_val);

    let remaining = next_node_size - size;

    let segment_node = unsafe { Segment::from_offset(self, next_node_offset, next_node_size) };

    // update the prev node to point to the next next node.
    let updated_prev = encode_segment_node(prev_node_size, next_next_node_offset);

    *prev_node.as_inner_ref_mut() = updated_prev;

    #[cfg(feature = "tracing")]
    tracing::debug!(
      "allocate {} bytes at offset {} from segment",
      size,
      next_node_offset
    );

    let mut memory_size = next_node_size;
    let data_end_offset = segment_node.data_offset + size;
    // check if the remaining is enough to allocate a new segment.
    if self.validate_segment(data_end_offset, remaining) {
      memory_size -= remaining;
      // We have successfully remove the head node from the list.
      // Then we can allocate the memory.
      // give back the remaining memory to the free list.

      // Safety: the `next + size` is in bounds, and `node_size - size` is also in bounds.
      self.pessimistic_dealloc(data_end_offset, remaining);
    }

    let mut allocated = Meta::new(self.ptr as _, segment_node.ptr_offset, memory_size);
    allocated.ptr_offset = segment_node.data_offset;
    allocated.ptr_size = size;
    unsafe {
      allocated.clear(self);
    }
    Ok(allocated)
  }

  /// It is like a pop operation, we will always allocate from the largest segment.
  fn alloc_slow_path_optimistic(&self, size: u32) -> Result<Meta, Error> {
    if self.ro {
      return Err(Error::ReadOnly);
    }

    let header = self.header();

    let sentinel = header.sentinel.as_inner_ref();
    let (sentinel_node_size, head_node_offset) = decode_segment_node(*sentinel);

    // free list is empty
    if sentinel_node_size == SENTINEL_SEGMENT_NODE_SIZE
      && head_node_offset == SENTINEL_SEGMENT_NODE_OFFSET
    {
      return Err(Error::InsufficientSpace {
        requested: size,
        available: self.remaining() as u32,
      });
    }

    let head = self.get_segment_node(head_node_offset);
    let head_node_size_and_next_node_offset = head.as_inner_ref();
    let (head_node_size, next_node_offset) =
      decode_segment_node(*head_node_size_and_next_node_offset);

    // The larget segment does not have enough space to allocate, so just return err.
    if size > head_node_size {
      return Err(Error::InsufficientSpace {
        requested: size,
        available: head_node_size,
      });
    }

    let remaining = head_node_size - size;

    // Safety: the `next` and `node_size` are valid, because they just come from the sentinel.
    let segment_node = unsafe { Segment::from_offset(self, head_node_offset, head_node_size) };

    *header.sentinel.as_inner_mut() = encode_segment_node(sentinel_node_size, next_node_offset);

    #[cfg(feature = "tracing")]
    tracing::debug!(
      "allocate {} bytes at offset {} from segment",
      size,
      segment_node.data_offset
    );

    let mut memory_size = head_node_size;
    let data_end_offset = segment_node.data_offset + size;
    // check if the remaining is enough to allocate a new segment.
    if self.validate_segment(data_end_offset, remaining) {
      memory_size -= remaining;
      // We have successfully remove the head node from the list.
      // Then we can allocate the memory.
      // give back the remaining memory to the free list.

      // Safety: the `next + size` is in bounds, and `node_size - size` is also in bounds.
      self.optimistic_dealloc(data_end_offset, remaining);
    }

    let mut allocated = Meta::new(self.ptr as _, segment_node.ptr_offset, memory_size);
    allocated.ptr_offset = segment_node.data_offset;
    allocated.ptr_size = size;
    unsafe {
      allocated.clear(self);
    }
    Ok(allocated)
  }

  fn discard_freelist_in(&self) -> u32 {
    let header = self.header();
    let mut discarded = 0;

    loop {
      let sentinel = header.sentinel.as_inner_ref();
      let (sentinel_node_size, head_node_offset) = decode_segment_node(*sentinel);

      // free list is empty
      if sentinel_node_size == SENTINEL_SEGMENT_NODE_SIZE
        && head_node_offset == SENTINEL_SEGMENT_NODE_OFFSET
      {
        return discarded;
      }

      let head = self.get_segment_node(head_node_offset);
      let head_node_size_and_next_node_offset = head.as_inner_ref();
      let (head_node_size, next_node_offset) =
        decode_segment_node(*head_node_size_and_next_node_offset);

      // Safety: the `next` and `node_size` are valid, because they just come from the sentinel.
      let segment_node = unsafe { Segment::from_offset(self, head_node_offset, head_node_size) };

      *header.sentinel.as_inner_mut() = encode_segment_node(sentinel_node_size, next_node_offset);

      // incresase the discarded memory.

      #[cfg(feature = "tracing")]
      tracing::debug!("discard {} bytes", segment_node.data_size);
      self.header_mut().discarded += segment_node.data_size;

      discarded += segment_node.data_size;
    }
  }

  /// Returns `true` if this offset and size is valid for a segment node.
  #[inline]
  fn validate_segment(&self, offset: u32, size: u32) -> bool {
    if offset == 0 || size == 0 {
      return false;
    }

    let aligned_offset = align_offset::<u64>(offset) as usize;
    let padding = aligned_offset - offset as usize;
    let segmented_node_size = padding + SEGMENT_NODE_SIZE;
    if segmented_node_size >= size as usize {
      return false;
    }

    let available_bytes = size - segmented_node_size as u32;
    if available_bytes < self.header().min_segment_size {
      return false;
    }

    true
  }

  #[inline]
  fn try_new_segment(&self, offset: u32, size: u32) -> Option<Segment> {
    if offset == 0 || size == 0 {
      return None;
    }

    let aligned_offset = align_offset::<u64>(offset) as usize;
    let padding = aligned_offset - offset as usize;
    let segmented_node_size = padding + SEGMENT_NODE_SIZE;
    if segmented_node_size >= size as usize {
      self.increase_discarded(size);
      return None;
    }

    let available_bytes = size - segmented_node_size as u32;
    if available_bytes < self.header().min_segment_size {
      self.increase_discarded(size);
      return None;
    }

    Some(Segment {
      ptr: self.ptr,
      ptr_offset: aligned_offset as u32,
      data_offset: (aligned_offset + SEGMENT_NODE_SIZE) as u32,
      data_size: available_bytes,
    })
  }

  #[inline]
  fn get_segment_node(&self, offset: u32) -> &UnsafeCell<u64> {
    // Safety: the offset is in bounds and well aligned.
    unsafe {
      let ptr = self.ptr.add(offset as usize);
      &*(ptr as *const _)
    }
  }

  #[inline]
  fn new_in(memory: Memory, max_retries: u8, unify: bool, ro: bool) -> Self {
    let ptr = memory.as_mut_ptr();

    Self {
      freelist: memory.freelist,
      cap: memory.cap(),
      flag: memory.flag,
      unify,
      magic_version: memory.magic_version,
      version: memory.version,
      ptr,
      ro,
      max_retries,
      data_offset: memory.data_offset as u32,
      inner: unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(memory)) as _) },
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      page_size: *PAGE_SIZE,
    }
  }

  #[inline]
  fn pad<T>() -> usize {
    let size = mem::size_of::<T>();
    let align = mem::align_of::<T>();
    size + align - 1
  }

  #[cfg(test)]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[inline]
  fn check_page_boundary(&self, offset: u32, len: u32) {
    if len == 0 {
      return; // A zero-length range is trivially within the same "page"
    }

    // Calculate the page boundary of the start and end of the range
    let start_page = offset / self.page_size;
    let end_page = (offset + len - 1) / self.page_size;

    assert_eq!(
      start_page, end_page,
      "start and end of range must be in the same page"
    );
  }

  #[cfg(test)]
  #[cfg(feature = "std")]
  #[allow(dead_code)]
  pub(super) fn print_segment_list(&self) {
    let header = self.header();
    let mut current: &UnsafeCell<u64> = &header.sentinel;

    loop {
      let current_node = current.as_inner_ref();
      let (node_size, next_node_offset) = decode_segment_node(*current_node);

      if node_size == SENTINEL_SEGMENT_NODE_SIZE {
        if next_node_offset == SENTINEL_SEGMENT_NODE_OFFSET {
          break;
        }

        current = self.get_segment_node(next_node_offset);
        continue;
      }

      std::println!("node_size: {node_size}, next_node_offset: {next_node_offset}",);

      if next_node_offset == SENTINEL_SEGMENT_NODE_OFFSET {
        break;
      }
      current = self.get_segment_node(next_node_offset);
    }
  }
}

impl Drop for Arena {
  fn drop(&mut self) {
    unsafe {
      let memory_ptr = self.inner.as_ptr();
      let memory = &mut *memory_ptr;
      // `Memory` storage... follow the drop steps from Arc.
      if memory.refs != 1 {
        memory.refs -= 1;
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
      // Drop the data
      let mut memory = Box::from_raw(memory_ptr);

      // Relaxed is enough here as we're in a drop, no one else can
      // access this memory anymore.
      memory.unmount();
    }
  }
}

#[cfg(test)]
mod tests;
