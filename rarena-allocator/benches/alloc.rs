use criterion::*;
use rarena_allocator::{Allocator, Buffer, Freelist, Options};
use std::sync::{Arc, Mutex, atomic::*};
use std::thread;

// --- Helpers ---

fn make_sync_arena(cap: u32, freelist: Freelist) -> rarena_allocator::sync::Arena {
  Options::new()
    .with_capacity(cap)
    .with_freelist(freelist)
    .alloc::<rarena_allocator::sync::Arena>()
    .unwrap()
}

fn make_unsync_arena(cap: u32, freelist: Freelist) -> rarena_allocator::unsync::Arena {
  Options::new()
    .with_capacity(cap)
    .with_freelist(freelist)
    .alloc::<rarena_allocator::unsync::Arena>()
    .unwrap()
}

/// A simple bump allocator behind a std::sync::Mutex, for comparison.
/// The buffer lives inside the lock, so callers must hold the lock
/// to both allocate and write — matching real-world `Mutex<Vec<u8>>` usage.
struct MutexBumpAlloc {
  inner: Mutex<MutexBumpInner>,
}

struct MutexBumpInner {
  buf: Vec<u8>,
  offset: usize,
}

impl MutexBumpAlloc {
  fn new(cap: usize) -> Self {
    Self {
      inner: Mutex::new(MutexBumpInner {
        buf: vec![0u8; cap],
        offset: 0,
      }),
    }
  }

  /// Allocate and fill the buffer while holding the lock.
  /// This is the realistic pattern: with `Mutex<Vec<u8>>`, you cannot
  /// release the lock and then write to the buffer.
  fn alloc_and_fill(&self, size: usize, fill: u8) -> Option<usize> {
    let mut inner = self.inner.lock().unwrap();
    let start = inner.offset;
    let end = start + size;
    if end > inner.buf.len() {
      return None;
    }
    inner.offset = end;
    // Simulate work: fill the allocated region while holding the lock.
    inner.buf[start..end].fill(fill);
    Some(start)
  }
}

/// Same but with parking_lot::Mutex.
struct ParkingLotBumpAlloc {
  inner: parking_lot::Mutex<ParkingLotBumpInner>,
}

struct ParkingLotBumpInner {
  buf: Vec<u8>,
  offset: usize,
}

impl ParkingLotBumpAlloc {
  fn new(cap: usize) -> Self {
    Self {
      inner: parking_lot::Mutex::new(ParkingLotBumpInner {
        buf: vec![0u8; cap],
        offset: 0,
      }),
    }
  }

  /// Allocate and fill while holding the lock.
  fn alloc_and_fill(&self, size: usize, fill: u8) -> Option<usize> {
    let mut inner = self.inner.lock();
    let start = inner.offset;
    let end = start + size;
    if end > inner.buf.len() {
      return None;
    }
    inner.offset = end;
    inner.buf[start..end].fill(fill);
    Some(start)
  }
}

// --- Realistic workload: alloc + fill buffer ---
// Arena: alloc (CAS), then fill the returned buffer without any lock.
// Mutex: alloc + fill while holding the lock (because the buffer is inside the mutex).

fn bench_alloc_and_fill_contention_nt(c: &mut Criterion, n_threads: usize) {
  let arena_cap = if n_threads >= 50 {
    1u32 << 30
  } else {
    512 << 20
  };
  let alloc_cap = arena_cap as usize;
  let group_name = format!("alloc_fill_{}t", n_threads);
  let mut group = c.benchmark_group(&group_name);
  if n_threads >= 50 {
    group.sample_size(10);
  }
  let bg_threads = n_threads - 1;
  for &size in &[32u32, 128, 512, 4096] {
    // Arena: alloc + fill outside lock
    group.bench_with_input(BenchmarkId::new("arena", size), &size, |b, &size| {
      b.iter_batched(
        || {
          let arena = make_sync_arena(arena_cap, Freelist::Discard);
          let stop = Arc::new(AtomicBool::new(false));
          let mut handles = Vec::new();
          for _ in 0..bg_threads {
            let a = arena.clone();
            let s = stop.clone();
            handles.push(thread::spawn(move || {
              while !s.load(Ordering::Relaxed) {
                if let Ok(mut buf) = a.alloc_bytes(size) {
                  // Fill outside any lock — other threads can allocate concurrently
                  buf.fill(0x42);
                }
              }
            }));
          }
          (arena, stop, handles)
        },
        |(arena, stop, handles)| {
          for i in 0..1000u32 {
            if let Ok(mut buf) = arena.alloc_bytes(size) {
              buf.fill(i as u8);
            }
          }
          stop.store(true, Ordering::Relaxed);
          for h in handles {
            h.join().unwrap();
          }
        },
        BatchSize::SmallInput,
      );
    });
    // std::sync::Mutex: alloc + fill under lock
    group.bench_with_input(BenchmarkId::new("std_mutex", size), &size, |b, &size| {
      b.iter_batched(
        || {
          let alloc = Arc::new(MutexBumpAlloc::new(alloc_cap));
          let stop = Arc::new(AtomicBool::new(false));
          let mut handles = Vec::new();
          for _ in 0..bg_threads {
            let a = alloc.clone();
            let s = stop.clone();
            handles.push(thread::spawn(move || {
              while !s.load(Ordering::Relaxed) {
                let _ = a.alloc_and_fill(size as usize, 0x42);
              }
            }));
          }
          (alloc, stop, handles)
        },
        |(alloc, stop, handles)| {
          for i in 0..1000u32 {
            let _ = alloc.alloc_and_fill(size as usize, i as u8);
          }
          stop.store(true, Ordering::Relaxed);
          for h in handles {
            h.join().unwrap();
          }
        },
        BatchSize::SmallInput,
      );
    });
    // parking_lot::Mutex: alloc + fill under lock
    group.bench_with_input(
      BenchmarkId::new("parking_lot_mutex", size),
      &size,
      |b, &size| {
        b.iter_batched(
          || {
            let alloc = Arc::new(ParkingLotBumpAlloc::new(alloc_cap));
            let stop = Arc::new(AtomicBool::new(false));
            let mut handles = Vec::new();
            for _ in 0..bg_threads {
              let a = alloc.clone();
              let s = stop.clone();
              handles.push(thread::spawn(move || {
                while !s.load(Ordering::Relaxed) {
                  let _ = a.alloc_and_fill(size as usize, 0x42);
                }
              }));
            }
            (alloc, stop, handles)
          },
          |(alloc, stop, handles)| {
            for i in 0..1000u32 {
              let _ = alloc.alloc_and_fill(size as usize, i as u8);
            }
            stop.store(true, Ordering::Relaxed);
            for h in handles {
              h.join().unwrap();
            }
          },
          BatchSize::SmallInput,
        );
      },
    );
  }
  group.finish();
}

fn bench_alloc_fill_1t(c: &mut Criterion) {
  bench_alloc_and_fill_contention_nt(c, 1);
}

fn bench_alloc_fill_2t(c: &mut Criterion) {
  bench_alloc_and_fill_contention_nt(c, 2);
}

fn bench_alloc_fill_4t(c: &mut Criterion) {
  bench_alloc_and_fill_contention_nt(c, 4);
}

fn bench_alloc_fill_8t(c: &mut Criterion) {
  bench_alloc_and_fill_contention_nt(c, 8);
}

fn bench_alloc_fill_50t(c: &mut Criterion) {
  bench_alloc_and_fill_contention_nt(c, 50);
}

fn bench_alloc_fill_100t(c: &mut Criterion) {
  bench_alloc_and_fill_contention_nt(c, 100);
}

// --- Freelist benchmarks (arena-only, no mutex equivalent) ---

fn bench_sync_alloc_dealloc_optimistic(c: &mut Criterion) {
  let mut group = c.benchmark_group("freelist_optimistic");
  for &size in &[64u32, 256, 1024] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || {
          let arena = make_sync_arena(64 << 20, Freelist::Optimistic);
          let mut offsets = Vec::new();
          for _ in 0..500 {
            let mut bytes = arena.alloc_bytes(size).unwrap();
            offsets.push((bytes.buffer_offset() as u32, bytes.buffer_capacity() as u32));
            unsafe {
              bytes.detach();
            }
          }
          for (offset, sz) in offsets {
            unsafe {
              arena.dealloc(offset, sz);
            }
          }
          arena
        },
        |arena| {
          for _ in 0..500 {
            let _ = arena.alloc_bytes(size);
          }
        },
        BatchSize::SmallInput,
      );
    });
  }
  group.finish();
}

fn bench_sync_alloc_dealloc_pessimistic(c: &mut Criterion) {
  let mut group = c.benchmark_group("freelist_pessimistic");
  for &size in &[64u32, 256, 1024] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || {
          let arena = make_sync_arena(64 << 20, Freelist::Pessimistic);
          let mut offsets = Vec::new();
          for _ in 0..500 {
            let mut bytes = arena.alloc_bytes(size).unwrap();
            offsets.push((bytes.buffer_offset() as u32, bytes.buffer_capacity() as u32));
            unsafe {
              bytes.detach();
            }
          }
          for (offset, sz) in offsets {
            unsafe {
              arena.dealloc(offset, sz);
            }
          }
          arena
        },
        |arena| {
          for _ in 0..500 {
            let _ = arena.alloc_bytes(size);
          }
        },
        BatchSize::SmallInput,
      );
    });
  }
  group.finish();
}

fn bench_unsync_alloc_dealloc(c: &mut Criterion) {
  let mut group = c.benchmark_group("unsync_freelist");
  for &(fl_name, fl) in &[
    ("optimistic", Freelist::Optimistic),
    ("pessimistic", Freelist::Pessimistic),
  ] {
    for &size in &[64u32, 256, 1024] {
      group.bench_with_input(
        BenchmarkId::new(fl_name, size),
        &(fl, size),
        |b, &(fl, size)| {
          b.iter_batched(
            || {
              let arena = make_unsync_arena(64 << 20, fl);
              let mut offsets = Vec::new();
              for _ in 0..500 {
                let mut bytes = arena.alloc_bytes(size).unwrap();
                offsets.push((bytes.buffer_offset() as u32, bytes.buffer_capacity() as u32));
                unsafe {
                  bytes.detach();
                }
              }
              for (offset, sz) in offsets {
                unsafe {
                  arena.dealloc(offset, sz);
                }
              }
              arena
            },
            |arena| {
              for _ in 0..500 {
                let _ = arena.alloc_bytes(size);
              }
            },
            BatchSize::SmallInput,
          );
        },
      );
    }
  }
  group.finish();
}

fn bench_sync_alloc_dealloc_contended(c: &mut Criterion) {
  let mut group = c.benchmark_group("freelist_contended");
  for &freelist in &[Freelist::Optimistic, Freelist::Pessimistic] {
    let name = match freelist {
      Freelist::Optimistic => "optimistic",
      Freelist::Pessimistic => "pessimistic",
      _ => unreachable!(),
    };
    group.bench_with_input(BenchmarkId::from_parameter(name), &freelist, |b, &fl| {
      let size = 128u32;
      b.iter_batched(
        || {
          let arena = make_sync_arena(256 << 20, fl);
          let mut offsets = Vec::new();
          for _ in 0..2000 {
            let mut bytes = arena.alloc_bytes(size).unwrap();
            offsets.push((bytes.buffer_offset() as u32, bytes.buffer_capacity() as u32));
            unsafe {
              bytes.detach();
            }
          }
          for (offset, sz) in offsets {
            unsafe {
              arena.dealloc(offset, sz);
            }
          }
          let arena2 = arena.clone();
          let stop = Arc::new(AtomicBool::new(false));
          let s = stop.clone();
          let handle = thread::spawn(move || {
            while !s.load(Ordering::Relaxed) {
              let _ = arena2.alloc_bytes(size);
            }
          });
          (arena, stop, handle)
        },
        |(arena, stop, handle)| {
          for _ in 0..500 {
            let _ = arena.alloc_bytes(size);
          }
          stop.store(true, Ordering::Relaxed);
          handle.join().unwrap();
        },
        BatchSize::SmallInput,
      );
    });
  }
  group.finish();
}

// --- Misc ---

fn bench_sync_read_write_u8(c: &mut Criterion) {
  c.bench_function("sync_read_write_u8", |b| {
    b.iter_batched(
      || {
        let arena = make_sync_arena(1 << 20, Freelist::Discard);
        for _ in 0..100 {
          let _ = arena.alloc_bytes(64).unwrap();
        }
        arena
      },
      |arena| {
        for i in 0..1000u32 {
          let offset = arena.data_offset() + (i as usize % 100) * 64;
          let _ = arena.get_u8(offset);
        }
      },
      BatchSize::SmallInput,
    );
  });
}

fn bench_sync_alloc_aligned(c: &mut Criterion) {
  let mut group = c.benchmark_group("sync_alloc_aligned");
  for &size in &[0u32, 64, 256] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || make_sync_arena(256 << 20, Freelist::Discard),
        |arena| {
          for _ in 0..1000 {
            let _ = arena.alloc_aligned_bytes::<u64>(size).unwrap();
          }
        },
        BatchSize::SmallInput,
      );
    });
  }
  group.finish();
}

criterion_group!(
  benches,
  // Realistic workload: alloc + fill (arena releases lock before fill, mutex holds it)
  bench_alloc_fill_1t,
  bench_alloc_fill_2t,
  bench_alloc_fill_4t,
  bench_alloc_fill_8t,
  bench_alloc_fill_50t,
  bench_alloc_fill_100t,
  // Aligned alloc & read/write
  bench_sync_alloc_aligned,
  bench_sync_read_write_u8,
  // Freelist (arena-specific)
  bench_sync_alloc_dealloc_optimistic,
  bench_sync_alloc_dealloc_pessimistic,
  bench_unsync_alloc_dealloc,
  bench_sync_alloc_dealloc_contended,
);
criterion_main!(benches);
