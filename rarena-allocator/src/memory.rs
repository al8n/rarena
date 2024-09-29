use core::{marker::PhantomData, ptr, slice};

use either::Either;

#[cfg(all(feature = "memmap", not(target_family = "wasm")))]
use memmap2::MmapOptions;

use super::{
  common::*,
  sealed::{Header, PathRefCounter, RefCounter},
  *,
};

enum MemoryBackend<P: PathRefCounter> {
  #[allow(dead_code)]
  Vec(AlignedVec, PhantomData<P>),
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  MmapMut {
    path: P,
    buf: *mut memmap2::MmapMut,
    file: std::fs::File,
    opts: Options,
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
    buf: memmap2::MmapMut,
    opts: Options,
  },
}

pub(crate) struct Memory<R, P: PathRefCounter, H> {
  refs: R,
  reserved: usize,
  cap: u32,
  header_offset: usize,
  data_offset: usize,
  lock_meta: bool,
  pub(crate) flag: MemoryFlags,
  header_ptr: Either<u32, H>,
  ptr: *mut u8,
  #[allow(dead_code)]
  backend: MemoryBackend<P>,
  unify: bool,
  magic_version: u16,
  version: u16,
  freelist: Freelist,
  read_only: bool,
  max_retries: u8,
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

  #[inline]
  pub(crate) const fn maximum_retries(&self) -> u8 {
    self.max_retries
  }

  #[inline]
  pub(crate) const fn read_only(&self) -> bool {
    self.read_only
  }

  #[inline]
  pub(crate) const fn unify(&self) -> bool {
    self.unify || self.flag.contains(MemoryFlags::ON_DISK)
  }

  #[inline]
  #[cfg(not(all(feature = "memmap", not(target_family = "wasm"))))]
  pub(crate) fn truncate(&mut self, allocated: usize, size: usize) {
    match &mut self.backend {
      MemoryBackend::Vec(aligned_vec, _) => {
        let mut new = AlignedVec::new::<H>(size, aligned_vec.align);

        unsafe {
          new
            .as_mut_ptr()
            .copy_from(aligned_vec.as_mut_ptr(), allocated);
        }

        *aligned_vec = new;
      }
    }
  }

  #[inline]
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn truncate(&mut self, allocated: usize, size: usize) -> std::io::Result<()> {
    match &mut self.backend {
      MemoryBackend::Vec(aligned_vec, _) => {
        let new = AlignedVec::new::<H>(size, aligned_vec.align);

        unsafe {
          let ptr = new.ptr.as_ptr();
          ptr::copy_nonoverlapping(aligned_vec.ptr.as_ptr(), ptr, allocated);
          self.ptr = ptr;
        }

        *aligned_vec = new;
      }
      MemoryBackend::MmapMut {
        buf, file, opts, ..
      } => unsafe {
        let _ = Box::from_raw(*buf);

        let current_file_size = file.metadata()?.len();
        if current_file_size < opts.offset + size as u64 {
          file.set_len(opts.offset + size as u64)?;
        }

        let mut mmap = mmap_mut(opts.with_capacity(size as u32).to_mmap_options(), file)?;
        let ptr = mmap.as_mut_ptr();
        *buf = Box::into_raw(Box::new(mmap));
        self.ptr = ptr;
      },
      MemoryBackend::Mmap { .. } => return Ok(()),
      MemoryBackend::AnonymousMmap { buf, opts } => {
        opts
          .with_capacity(size as u32)
          .to_mmap_options()
          .map_anon()
          .map(|mut new| {
            new[..allocated].copy_from_slice(&buf[..allocated]);
            self.ptr = new.as_mut_ptr();
            *buf = new;
          })?;
      }
    }

    self.cap = size as u32;

    Ok(())
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
      (Either::Left(header_ptr_offset as u32), data_offset)
    } else {
      (
        Either::Right(H::new(self.reserved as u32 + 1, min_segment_size)),
        self.reserved + 1,
      )
    };

    self.header_ptr = header;
    self.data_offset = data_offset;
  }

  pub(crate) fn alloc(opts: Options) -> Result<Self, Error> {
    let vec_cap = opts.capacity();
    let alignment = opts.maximum_alignment().max(8);
    let min_segment_size = opts.minimum_segment_size();
    let unify = opts.unify();
    let reserved = opts.reserved() as usize;
    let header_ptr_offset = check_capacity::<H>(reserved, unify, vec_cap as usize)?;

    let mut vec = AlignedVec::new::<H>(vec_cap as usize, alignment);
    // Safety: we have add the overhead for the header
    unsafe {
      let ptr = vec.as_mut_ptr();
      ptr::write_bytes(ptr, 0, vec.cap);

      let mut data_offset = header_ptr_offset + mem::size_of::<H>();
      let header_ptr = ptr.add(header_ptr_offset).cast::<H>();

      let (header, data_offset) = if unify {
        super::write_sanity(
          opts.freelist() as u8,
          opts.magic_version(),
          slice::from_raw_parts_mut(ptr.add(reserved), 8),
        );
        header_ptr.write(H::new(data_offset as u32, min_segment_size));
        (Either::Left(header_ptr_offset as _), data_offset)
      } else {
        data_offset = reserved + 1;
        (
          Either::Right(H::new((reserved + 1) as u32, min_segment_size)),
          data_offset,
        )
      };

      Ok(Self {
        cap: vec_cap,
        lock_meta: false,
        header_offset: header_ptr_offset,
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
        read_only: false,
        max_retries: opts.maximum_retries(),
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_mut<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
  ) -> std::io::Result<Self> {
    Self::map_mut_in(path.as_ref().to_path_buf(), opts, mmap_mut)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_mut_with_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_mut_in(path, opts, mmap_mut).map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
  ) -> std::io::Result<Self> {
    Self::map_mut_in(path.as_ref().to_path_buf(), opts, mmap_copy)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy_with_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_mut_in(path, opts, mmap_copy).map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_mut_in(
    path: std::path::PathBuf,
    opts: Options,
    f: impl FnOnce(MmapOptions, &std::fs::File) -> std::io::Result<memmap2::MmapMut>,
  ) -> std::io::Result<Self> {
    let (create_new, file) = opts.open(path.as_path())?;
    let file_size = file.metadata()?.len();
    let reserved = opts.reserved() as usize;

    let min_segment_size = opts.minimum_segment_size();
    let freelist = opts.freelist();
    let magic_version = opts.magic_version();
    let lock_meta = opts.lock_meta();

    if !create_new {
      let (_, prefix_size) = header_meta::<H>(reserved, true);
      if file_size.checked_sub(opts.offset).unwrap_or_default() < prefix_size as u64 {
        return Err(invalid_input("file is not in a valid layout"));
      }
    }

    if let Some(cap) = opts.capacity {
      if file_size < opts.offset + cap as u64 {
        file.set_len(opts.offset + cap as u64)?;
      }
    }

    unsafe {
      f(opts.to_mmap_options(), &file).and_then(|mut mmap| {
        let cap = mmap.len();

        let header_ptr_offset = check_capacity::<H>(reserved, true, cap).map_err(invalid_input)?;

        let ptr = mmap.as_mut_ptr();

        // if the file is newly created, we need to initialize the memory
        if create_new {
          ptr::write_bytes(ptr, 0, cap);
        }

        let reserved = opts.reserved() as usize;

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
          ptr::write_bytes(ptr.add(allocated as usize), 0, cap - allocated as usize);
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
          header_offset: header_ptr_offset,
          lock_meta,
          flag: MemoryFlags::ON_DISK | MemoryFlags::MMAP,
          backend: MemoryBackend::MmapMut {
            remove_on_drop: AtomicBool::new(false),
            path: PR::new(path),
            buf: Box::into_raw(Box::new(mmap)),
            opts,
            file,
          },
          header_ptr: Either::Left(header_ptr_offset as _),
          ptr,
          refs: R::new(1),
          data_offset,
          unify: true,
          magic_version,
          version,
          freelist,
          read_only: false,
          max_retries: opts.maximum_retries(),
        };

        if lock_meta {
          this.mlock(header_ptr_offset, mem::size_of::<H>())?;
        }

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_with_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_in(path, opts, mmap).map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map<P: AsRef<std::path::Path>>(path: P, opts: Options) -> std::io::Result<Self> {
    Self::map_in(path.as_ref().to_path_buf(), opts, mmap)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy_read_only_with_path_builder<PB, E>(
    path_builder: PB,
    opts: Options,
  ) -> Result<Self, Either<E, std::io::Error>>
  where
    PB: FnOnce() -> Result<std::path::PathBuf, E>,
  {
    let path = path_builder().map_err(Either::Left)?;

    Self::map_in(path, opts, mmap_copy_read_only).map_err(Either::Right)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_copy_read_only<P: AsRef<std::path::Path>>(
    path: P,
    opts: Options,
  ) -> std::io::Result<Self> {
    Self::map_in(path.as_ref().to_path_buf(), opts, mmap_copy_read_only)
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_in(
    path: std::path::PathBuf,
    opts: Options,
    f: impl FnOnce(MmapOptions, &std::fs::File) -> std::io::Result<memmap2::Mmap>,
  ) -> std::io::Result<Self> {
    use either::Either;

    if !path.exists() {
      return Err(std::io::Error::new(
        std::io::ErrorKind::NotFound,
        "file not found",
      ));
    }

    // clear write permissions
    let opts = opts
      .with_create(false)
      .with_create_new(false)
      .with_write(false)
      .with_append(false)
      .with_truncate(false);

    let (_, file) = opts.open(&path)?;
    let reserved = opts.reserved();
    let magic_version = opts.magic_version();

    let size = file.metadata()?.len();
    let mmap_opts = {
      let mut mopts = MmapOptions::new();
      if opts.populate() {
        mopts.populate();
      }

      let offset = opts.offset();
      if offset > 0 {
        mopts.offset(offset);
      }

      if let Some(cap) = opts.capacity {
        mopts.len((size - offset).min(cap as u64) as usize);
      }
      mopts
    };

    let (_, prefix_size) = header_meta::<H>(reserved as usize, true);
    if size.checked_sub(opts.offset).unwrap_or_default() < prefix_size as u64 {
      return Err(invalid_input("file is not in a valid layout"));
    }

    unsafe {
      f(mmap_opts, &file).and_then(|mmap| {
        let len = mmap.len();
        let reserved = reserved as usize;

        let header_ptr_offset = check_capacity::<H>(reserved, true, len).map_err(invalid_input)?;

        let ptr = mmap.as_ptr();

        let freelist = super::sanity_check(
          None,
          magic_version,
          &mmap[reserved..reserved + mem::align_of::<H>()],
        )?;
        let data_offset = header_ptr_offset + mem::size_of::<H>();

        let this = Self {
          cap: len as u32,
          reserved,
          header_offset: header_ptr_offset,
          flag: MemoryFlags::ON_DISK | MemoryFlags::MMAP,
          backend: MemoryBackend::Mmap {
            remove_on_drop: AtomicBool::new(false),
            path: PR::new(path),
            buf: Box::into_raw(Box::new(mmap)),
            file,
          },
          header_ptr: Either::Left(header_ptr_offset as u32),
          ptr: ptr as _,
          refs: R::new(1),
          data_offset,
          unify: true,
          magic_version,
          version: CURRENT_VERSION,
          freelist,
          read_only: true,
          max_retries: opts.maximum_retries(),
          lock_meta: opts.lock_meta(),
        };

        if this.lock_meta {
          this.mlock(header_ptr_offset, mem::size_of::<H>())?;
        }

        Ok(this)
      })
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn map_anon(opts: Options) -> std::io::Result<Self> {
    opts.to_mmap_options().map_anon().and_then(|mut mmap| {
      let map_cap = mmap.len();

      let alignment = opts.maximum_alignment().max(mem::align_of::<H>());

      let freelist = opts.freelist();
      let min_segment_size = opts.minimum_segment_size();
      let unify = opts.unify();
      let reserved = opts.reserved();
      let magic_version = opts.magic_version();

      let header_ptr_offset =
        check_capacity::<H>(reserved as usize, unify, map_cap).map_err(invalid_input)?;

      // TODO:  should we align the memory?
      let _alignment = alignment.max(mem::align_of::<H>());
      let ptr = mmap.as_mut_ptr();

      // Safety: we have add the overhead for the header
      unsafe {
        ptr::write_bytes(ptr, 0, map_cap);

        let mut data_offset = header_ptr_offset + mem::size_of::<H>();
        let header_ptr = ptr.add(header_ptr_offset);

        let (header, data_offset) = if unify {
          super::write_sanity(
            freelist as u8,
            magic_version,
            slice::from_raw_parts_mut(ptr.add(reserved as usize), mem::align_of::<H>()),
          );
          header_ptr
            .cast::<H>()
            .write(H::new(data_offset as u32, min_segment_size));
          (Either::Left(header_ptr_offset as _), data_offset)
        } else {
          data_offset = reserved as usize + 1;
          (
            Either::Right(H::new(reserved + 1, min_segment_size)),
            data_offset,
          )
        };

        let this = Self {
          reserved: reserved as usize,
          header_offset: header_ptr_offset,
          flag: MemoryFlags::MMAP,
          cap: map_cap as u32,
          backend: MemoryBackend::AnonymousMmap { buf: mmap, opts },
          refs: R::new(1),
          data_offset,
          header_ptr: header,
          ptr,
          unify,
          magic_version,
          version: CURRENT_VERSION,
          freelist,
          read_only: false,
          max_retries: opts.maximum_retries(),
          lock_meta: opts.lock_meta(),
        };

        if this.lock_meta {
          this.mlock(header_ptr_offset, mem::size_of::<H>())?;
        }

        Ok(this)
      }
    })
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.lock_exclusive(),
      MemoryBackend::Mmap { file, .. } => file.lock_exclusive(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn lock_shared(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.lock_shared(),
      MemoryBackend::Mmap { file, .. } => file.lock_shared(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn try_lock_exclusive(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.try_lock_exclusive(),
      MemoryBackend::Mmap { file, .. } => file.try_lock_exclusive(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn try_lock_shared(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.try_lock_shared(),
      MemoryBackend::Mmap { file, .. } => file.try_lock_shared(),
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn unlock(&self) -> std::io::Result<()> {
    use fs4::fs_std::FileExt;
    match &self.backend {
      MemoryBackend::MmapMut { file, .. } => file.unlock(),
      MemoryBackend::Mmap { file, .. } => file.unlock(),
      _ => Ok(()),
    }
  }

  /// ## Safety
  /// - offset and len must be valid and in bounds.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) unsafe fn mlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    #[cfg(not(windows))]
    match &self.backend {
      MemoryBackend::MmapMut { buf, .. } => {
        let buf = &**buf;
        let buf_len = buf.len();
        if offset + len > buf_len {
          return Err(range_out_of_bounds(offset, len, buf_len));
        }

        let ptr = buf.as_ptr().add(offset);
        rustix::mm::mlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      MemoryBackend::Mmap { buf, .. } => {
        let buf = &**buf;
        let buf_len = buf.len();
        if offset + len > buf_len {
          return Err(range_out_of_bounds(offset, len, buf_len));
        }

        let ptr = buf.as_ref().as_ptr().add(offset);
        rustix::mm::mlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      MemoryBackend::AnonymousMmap { buf, .. } => {
        let buf_len = buf.len();
        if offset + len > buf_len {
          return Err(range_out_of_bounds(offset, len, buf_len));
        }

        let ptr = buf.as_ref().as_ptr().add(offset);
        rustix::mm::mlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      _ => Ok(()),
    }

    #[cfg(windows)]
    {
      let _ = offset;
      let _ = len;
      Ok(())
    }
  }

  /// ## Safety
  /// - offset and len must be valid and in bounds.
  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) unsafe fn munlock(&self, offset: usize, len: usize) -> std::io::Result<()> {
    #[cfg(not(windows))]
    match &self.backend {
      MemoryBackend::MmapMut { buf, .. } => {
        let buf = &**buf;
        let buf_len = buf.len();
        if offset + len > buf_len {
          return Err(range_out_of_bounds(offset, len, buf_len));
        }

        let ptr = buf.as_ref().as_ptr().add(offset);
        rustix::mm::munlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      MemoryBackend::Mmap { buf, .. } => {
        let buf = &**buf;
        let buf_len = buf.len();
        if offset + len > buf_len {
          return Err(range_out_of_bounds(offset, len, buf_len));
        }

        let ptr = buf.as_ref().as_ptr().add(offset);
        rustix::mm::munlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      MemoryBackend::AnonymousMmap { buf, .. } => {
        let buf_len = buf.len();
        if offset + len > buf_len {
          return Err(range_out_of_bounds(offset, len, buf_len));
        }

        let ptr = buf.as_ref().as_ptr().add(offset);
        rustix::mm::munlock(ptr as _, len)
          .map_err(|e| std::io::Error::from_raw_os_error(e.raw_os_error()))
      }
      _ => Ok(()),
    }

    #[cfg(windows)]
    {
      let _ = offset;
      let _ = len;
      Ok(())
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
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe {
        let mmap = &**mmap;
        let mmap_len = mmap.len();
        if offset + len > mmap_len {
          return Err(range_out_of_bounds(offset, len, mmap_len));
        }

        mmap.flush_range(offset, len)
      },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  pub(crate) fn flush_async_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe {
        let mmap = &**mmap;
        let mmap_len = mmap.len();
        if offset + len > mmap_len {
          return Err(range_out_of_bounds(offset, len, mmap_len));
        }

        mmap.flush_async_range(offset, len)
      },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub(crate) fn flush_header_and_range(&self, offset: usize, len: usize) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe {
        let mmap = &**mmap;
        let mmap_len = mmap.len();
        if len == 0 {
          return mmap.flush_range(self.header_offset, mem::size_of::<H>());
        }

        if offset + len > mmap_len {
          return Err(range_out_of_bounds(offset, len, mmap_len));
        }

        let header_offset = self.header_offset;
        let header_size = mem::size_of::<H>();
        let page_size = (*PAGE_SIZE) as usize;

        let header_range_start = header_offset;
        let header_range_end = header_offset + header_size;
        let header_start_page = header_range_start / page_size;
        let header_end_page = (header_range_end + page_size - 1) / page_size;

        let flush_end = offset + len;
        let range_start_page = offset / page_size;
        let range_end_page = (flush_end + page_size - 1) / page_size;

        if header_start_page == range_start_page && header_end_page == range_end_page {
          let start = header_offset.min(offset);
          return mmap.flush_range(start, header_range_end.max(flush_end) - start);
        }

        if offset <= header_offset && header_range_end <= flush_end {
          return mmap.flush_range(offset, len);
        }

        mmap
          .flush_range(header_offset, header_size)
          .and_then(|_| mmap.flush_range(offset, len))
      },
      _ => Ok(()),
    }
  }

  #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
  #[cfg_attr(docsrs, doc(cfg(all(feature = "memmap", not(target_family = "wasm")))))]
  pub(crate) fn flush_async_header_and_range(
    &self,
    offset: usize,
    len: usize,
  ) -> std::io::Result<()> {
    match &self.backend {
      #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
      MemoryBackend::MmapMut { buf: mmap, .. } => unsafe {
        let mmap = &**mmap;
        let mmap_len = mmap.len();
        if len == 0 {
          return mmap.flush_async_range(self.header_offset, mem::size_of::<H>());
        }

        if offset + len > mmap_len {
          return Err(range_out_of_bounds(offset, len, mmap_len));
        }

        let header_offset = self.header_offset;
        let header_size = mem::size_of::<H>();
        let page_size = (*PAGE_SIZE) as usize;

        let header_range_start = header_offset;
        let header_range_end = header_offset + header_size;
        let header_start_page = header_range_start / page_size;
        let header_end_page = (header_range_end + page_size - 1) / page_size;

        let flush_end = offset + len;
        let range_start_page = offset / page_size;
        let range_end_page = (flush_end + page_size - 1) / page_size;

        if header_start_page == range_start_page && header_end_page == range_end_page {
          let start = header_offset.min(offset);
          return mmap.flush_async_range(start, header_range_end.max(flush_end) - start);
        }

        if offset <= header_offset && header_range_end <= flush_end {
          return mmap.flush_async_range(offset, len);
        }

        mmap
          .flush_async_range(header_offset, header_size)
          .and_then(|_| mmap.flush_async_range(offset, len))
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
        Either::Left(header_ptr_offset) => &*self.ptr.add(*header_ptr_offset as usize).cast::<H>(),
        Either::Right(header) => header,
      }
    }
  }

  #[inline]
  pub(crate) fn header_mut(&mut self) -> &mut H {
    unsafe {
      match &mut self.header_ptr {
        Either::Left(header_ptr_offset) => {
          &mut *self.ptr.add(*header_ptr_offset as usize).cast::<H>()
        }
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
    #[cfg(all(feature = "memmap", not(target_family = "wasm")))]
    if self.lock_meta {
      let _ = self.munlock(self.header_offset, mem::size_of::<H>());
    }

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
fn header_meta<H>(reserved: usize, unify: bool) -> (usize, usize) {
  if unify {
    let offset = align_offset::<H>(reserved as u32) as usize + mem::align_of::<H>();
    (offset, offset + mem::size_of::<H>())
  } else {
    (reserved + 1, reserved + 1)
  }
}

#[inline]
fn check_capacity<H>(reserved: usize, unify: bool, capacity: usize) -> Result<usize, Error> {
  let (header_ptr_offset, prefix_size) = header_meta::<H>(reserved, unify);

  if prefix_size > capacity {
    return Err(Error::InsufficientSpace {
      requested: prefix_size as u32,
      available: capacity as u32,
    });
  }

  Ok(header_ptr_offset)
}
