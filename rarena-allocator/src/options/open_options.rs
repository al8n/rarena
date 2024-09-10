use memmap2::MmapOptions as Mmap2Options;
use std::{
  fs::{File, OpenOptions as StdOpenOptions},
  io,
  path::Path,
};

/// Options for opening a file for memory mapping.
#[derive(Debug, Clone)]
pub struct OpenOptions {
  opts: StdOpenOptions,
  pub(crate) create: Option<u32>,
  pub(crate) create_new: Option<u32>,
}

impl From<StdOpenOptions> for OpenOptions {
  fn from(opts: StdOpenOptions) -> Self {
    Self {
      opts,
      create_new: None,
      create: None,
    }
  }
}

impl Default for OpenOptions {
  /// Creates a blank new set of options ready for configuration.
  ///
  /// All options are initially set to `false`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let options = OpenOptions::default();
  /// ```
  fn default() -> Self {
    Self::new()
  }
}

impl OpenOptions {
  /// Creates a blank new set of options ready for configuration.
  ///
  /// All options are initially set to `false`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let mut options = OpenOptions::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self {
      opts: StdOpenOptions::new(),
      create: None,
      create_new: None,
    }
  }

  /// Sets the option for read access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `read`-able if opened.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let opts = OpenOptions::new().read(true);
  /// ```
  #[inline]
  pub fn read(mut self, read: bool) -> Self {
    self.opts.read(read);
    self
  }

  /// Sets the option for write access.
  ///
  /// This option, when true, will indicate that the file should be
  /// `write`-able if opened.
  ///
  /// If the file already exists, any write calls on it will overwrite its
  /// contents, without truncating it.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true);
  /// ```
  #[inline]
  pub fn write(mut self, write: bool) -> Self {
    self.opts.write(write);
    self
  }

  /// Sets the option for the append mode.
  ///
  /// This option, when true, means that writes will append to a file instead
  /// of overwriting previous contents.
  /// Note that setting `.write(true).append(true)` has the same effect as
  /// setting only `.append(true)`.
  ///
  /// For most filesystems, the operating system guarantees that all writes are
  /// atomic: no writes get mangled because another process writes at the same
  /// time.
  ///
  /// One maybe obvious note when using append-mode: make sure that all data
  /// that belongs together is written to the file in one operation. This
  /// can be done by concatenating strings before passing them to [`write()`],
  /// or using a buffered writer (with a buffer of adequate size),
  /// and calling [`flush()`] when the message is complete.
  ///
  /// If a file is opened with both read and append access, beware that after
  /// opening, and after every write, the position for reading may be set at the
  /// end of the file. So, before writing, save the current position (using
  /// <code>[seek]\([SeekFrom](std::io::SeekFrom)::[Current]\(opts))</code>), and restore it before the next read.
  ///
  /// ## Note
  ///
  /// This function doesn't create the file if it doesn't exist. Use the
  /// [`OpenOptions::create`] method to do so.
  ///
  /// [`write()`]: std::io::Write::write "io::Write::write"
  /// [`flush()`]: std::io::Write::flush "io::Write::flush"
  /// [seek]: std::io::Seek::seek "io::Seek::seek"
  /// [Current]: std::io::SeekFrom::Current "io::SeekFrom::Current"
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let opts = OpenOptions::new().append(true);
  /// ```
  #[inline]
  pub fn append(mut self, append: bool) -> Self {
    self.opts.append(append);
    self
  }

  /// Sets the option for truncating a previous file.
  ///
  /// If a file is successfully opened with this option set it will truncate
  /// the file to opts length if it already exists.
  ///
  /// The file must be opened with write access for truncate to work.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true).truncate(true);
  /// ```
  #[inline]
  pub fn truncate(mut self, truncate: bool) -> Self {
    self.opts.truncate(truncate);
    self
  }

  /// Sets the option to create a new file, or open it if it already exists.
  /// If the file does not exist, it is created and set the lenght of the file to the given size.
  ///
  /// In order for the file to be created, [`OpenOptions::write`] or
  /// [`OpenOptions::append`] access must be used.
  ///
  /// See also [`std::fs::write()`][std::fs::write] for a simple function to
  /// create a file with some given data.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true).create(Some(1000));
  /// ```
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let opts = OpenOptions::new().write(true).create(None);
  /// ```
  #[inline]
  pub fn create(mut self, size: Option<u32>) -> Self {
    match size {
      Some(size) => {
        self.opts.create(true);
        self.create = Some(size);
      }
      None => {
        self.opts.create(false);
        self.create = None;
      }
    }
    self
  }

  /// Sets the option to create a new file and set the file length to the given value, failing if it already exists.
  ///
  /// No file is allowed to exist at the target location, also no (dangling) symlink. In this
  /// way, if the call succeeds, the file returned is guaranteed to be new.
  ///
  /// This option is useful because it is atomic. Otherwise between checking
  /// whether a file exists and creating a new one, the file may have been
  /// created by another process (a TOCTOU race condition / attack).
  ///
  /// If `.create_new(true)` is set, [`.create()`] and [`.truncate()`] are
  /// ignored.
  ///
  /// The file must be opened with write or append access in order to create
  /// a new file.
  ///
  /// [`.create()`]: OpenOptions::create
  /// [`.truncate()`]: OpenOptions::truncate
  ///
  /// # Examples
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let file = OpenOptions::new()
  ///   .write(true)
  ///   .create_new(Some(1000));
  /// ```
  ///
  /// ```rust
  /// use rarena_allocator::OpenOptions;
  ///
  /// let opts = OpenOptions::new()
  ///   .write(true)
  ///   .create_new(None);
  /// ```
  #[inline]
  pub fn create_new(mut self, size: Option<u32>) -> Self {
    match size {
      Some(size) => {
        self.opts.create_new(true);
        self.create_new = Some(size);
      }
      None => {
        self.opts.create_new(false);
        self.create_new = None;
      }
    }
    self
  }

  pub(crate) fn open<P: AsRef<Path>>(&self, path: P) -> io::Result<(bool, File)> {
    if let Some(size) = self.create_new {
      return self
        .opts
        .open(path)
        .and_then(|f| f.set_len(size as u64).map(|_| (true, f)));
    }

    if let Some(size) = self.create {
      return if path.as_ref().exists() {
        self.opts.open(path).map(|f| (false, f))
      } else {
        self
          .opts
          .open(path)
          .and_then(|f| f.set_len(size as u64).map(|_| (true, f)))
      };
    }

    self.opts.open(path).map(|f| (false, f))
  }
}

/// A memory map options for file backed [`SkipMap`](super::SkipMap),
/// providing advanced options and flags for specifying memory map behavior.
#[derive(Clone, Debug)]
pub struct MmapOptions(Mmap2Options);

impl Default for MmapOptions {
  fn default() -> Self {
    Self::new()
  }
}

impl From<Mmap2Options> for MmapOptions {
  fn from(opts: Mmap2Options) -> Self {
    Self(opts)
  }
}

impl MmapOptions {
  /// Creates a new set of options for configuring and creating a memory map.
  ///
  /// # Example
  ///
  /// ```rust
  /// use rarena_allocator::MmapOptions;
  ///
  /// // Create a new memory map options.
  /// let mut mmap_options = MmapOptions::new();
  /// ```
  #[inline]
  pub fn new() -> Self {
    Self(Mmap2Options::new())
  }

  /// Configures the created memory mapped buffer to be `len` bytes long.
  ///
  /// This option is mandatory for anonymous memory maps.
  ///
  /// For file-backed memory maps, the length will default to the file length.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::MmapOptions;
  ///
  /// let opts = MmapOptions::new().len(9);
  /// ```
  #[inline]
  pub fn len(mut self, len: u32) -> Self {
    self.0.len(len as usize);
    self
  }

  /// Configures the memory map to start at byte `offset` from the beginning of the file.
  ///
  /// This option has no effect on anonymous memory maps.
  ///
  /// By default, the offset is 0.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::MmapOptions;
  ///
  /// let opts = MmapOptions::new().offset(30);
  /// ```
  #[inline]
  pub fn offset(mut self, offset: u32) -> Self {
    self.0.offset(offset as u64);
    self
  }

  /// Configures the anonymous memory map to be suitable for a process or thread stack.
  ///
  /// This option corresponds to the `MAP_STACK` flag on Linux. It has no effect on Windows.
  ///
  /// This option has no effect on file-backed memory maps.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::MmapOptions;
  ///
  /// let stack = MmapOptions::new().stack();
  /// ```
  #[inline]
  pub fn stack(mut self) -> Self {
    self.0.stack();
    self
  }

  /// Configures the anonymous memory map to be allocated using huge pages.
  ///
  /// This option corresponds to the `MAP_HUGETLB` flag on Linux. It has no effect on Windows.
  ///
  /// The size of the requested page can be specified in page bits. If not provided, the system
  /// default is requested. The requested length should be a multiple of this, or the mapping
  /// will fail.
  ///
  /// This option has no effect on file-backed memory maps.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::MmapOptions;
  ///
  /// let stack = MmapOptions::new().huge(Some(21)).len(2*1024*1024);
  /// ```
  #[inline]
  pub fn huge(mut self, page_bits: Option<u8>) -> Self {
    self.0.huge(page_bits);
    self
  }

  /// Populate (prefault) page tables for a mapping.
  ///
  /// For a file mapping, this causes read-ahead on the file. This will help to reduce blocking on page faults later.
  ///
  /// This option corresponds to the `MAP_POPULATE` flag on Linux. It has no effect on Windows.
  ///
  /// # Example
  ///
  /// ```
  /// use rarena_allocator::MmapOptions;
  ///
  ///
  /// let opts = MmapOptions::new().populate();
  /// ```
  #[inline]
  pub fn populate(mut self) -> Self {
    self.0.populate();
    self
  }

  #[inline]
  pub(crate) unsafe fn map(&self, file: &File) -> io::Result<memmap2::Mmap> {
    self.0.map(file)
  }

  #[inline]
  pub(crate) unsafe fn map_mut(&self, file: &File) -> io::Result<memmap2::MmapMut> {
    self.0.map_mut(file)
  }

  #[inline]
  pub(crate) unsafe fn map_copy(&self, file: &File) -> io::Result<memmap2::MmapMut> {
    self.0.map_copy(file)
  }

  #[inline]
  pub(crate) unsafe fn map_copy_read_only(&self, file: &File) -> io::Result<memmap2::Mmap> {
    self.0.map_copy_read_only(file)
  }

  #[inline]
  pub(crate) fn map_anon(&self) -> io::Result<memmap2::MmapMut> {
    self.0.map_anon()
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_from() {
    let opts = StdOpenOptions::new();
    let _open_opts = OpenOptions::from(opts);

    let opts = Mmap2Options::new();
    let _mmap_opts = MmapOptions::from(opts);
  }
}
