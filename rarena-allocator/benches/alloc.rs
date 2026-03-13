use criterion::*;
use rarena_allocator::{Allocator, Buffer, Freelist, Options};
use std::sync::{Arc, atomic::*};
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

// --- Sync: alloc_bytes fast path (single thread, no contention) ---

fn bench_sync_alloc_bytes_no_contention(c: &mut Criterion) {
  let mut group = c.benchmark_group("sync_alloc_bytes_no_contention");
  for &size in &[32u32, 128, 512, 4096] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || make_sync_arena(256 << 20, Freelist::None),
        |arena| {
          for _ in 0..1000 {
            let _ = arena.alloc_bytes(size).unwrap();
          }
        },
        BatchSize::SmallInput,
      );
    });
  }
  group.finish();
}

// --- Sync: alloc_bytes with contention (2 threads) ---

fn bench_sync_alloc_bytes_contended(c: &mut Criterion) {
  let mut group = c.benchmark_group("sync_alloc_bytes_contended");
  for &size in &[32u32, 128, 512] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || {
          let arena = make_sync_arena(512 << 20, Freelist::None);
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
          for _ in 0..1000 {
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

// --- Sync: alloc_bytes high contention (4 threads) ---

fn bench_sync_alloc_bytes_high_contention(c: &mut Criterion) {
  let mut group = c.benchmark_group("sync_alloc_bytes_high_contention");
  for &size in &[32u32, 128, 512] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || {
          let arena = make_sync_arena(512 << 20, Freelist::None);
          let stop = Arc::new(AtomicBool::new(false));
          let mut handles = Vec::new();
          for _ in 0..3 {
            let a = arena.clone();
            let s = stop.clone();
            handles.push(thread::spawn(move || {
              while !s.load(Ordering::Relaxed) {
                let _ = a.alloc_bytes(size);
              }
            }));
          }
          (arena, stop, handles)
        },
        |(arena, stop, handles)| {
          for _ in 0..1000 {
            let _ = arena.alloc_bytes(size);
          }
          stop.store(true, Ordering::Relaxed);
          for h in handles {
            h.join().unwrap();
          }
        },
        BatchSize::SmallInput,
      );
    });
  }
  group.finish();
}

// --- Sync: alloc + dealloc with freelist ---

fn bench_sync_alloc_dealloc_optimistic(c: &mut Criterion) {
  let mut group = c.benchmark_group("sync_alloc_dealloc_optimistic");
  for &size in &[64u32, 256, 1024] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || {
          let arena = make_sync_arena(64 << 20, Freelist::Optimistic);
          // Pre-allocate and deallocate to populate freelist
          let mut offsets = Vec::new();
          for _ in 0..500 {
            let bytes = arena.alloc_bytes(size).unwrap();
            offsets.push((bytes.offset() as u32, size));
          }
          for (offset, sz) in offsets {
            unsafe {
              arena.dealloc(offset, sz);
            }
          }
          arena
        },
        |arena| {
          // Now allocate from freelist
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
  let mut group = c.benchmark_group("sync_alloc_dealloc_pessimistic");
  for &size in &[64u32, 256, 1024] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || {
          let arena = make_sync_arena(64 << 20, Freelist::Pessimistic);
          let mut offsets = Vec::new();
          for _ in 0..500 {
            let bytes = arena.alloc_bytes(size).unwrap();
            offsets.push((bytes.offset() as u32, size));
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

// --- Sync: alloc + dealloc with contention and freelist ---

fn bench_sync_alloc_dealloc_contended(c: &mut Criterion) {
  let mut group = c.benchmark_group("sync_alloc_dealloc_contended");
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
          // Pre-populate freelist
          let mut offsets = Vec::new();
          for _ in 0..2000 {
            let bytes = arena.alloc_bytes(size).unwrap();
            offsets.push((bytes.offset() as u32, size));
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

// --- Unsync: alloc_bytes (single thread baseline) ---

fn bench_unsync_alloc_bytes(c: &mut Criterion) {
  let mut group = c.benchmark_group("unsync_alloc_bytes");
  for &size in &[32u32, 128, 512, 4096] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || make_unsync_arena(256 << 20, Freelist::None),
        |arena| {
          for _ in 0..1000 {
            let _ = arena.alloc_bytes(size).unwrap();
          }
        },
        BatchSize::SmallInput,
      );
    });
  }
  group.finish();
}

// --- Unsync: alloc + dealloc with freelist ---

fn bench_unsync_alloc_dealloc(c: &mut Criterion) {
  let mut group = c.benchmark_group("unsync_alloc_dealloc");
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
                let bytes = arena.alloc_bytes(size).unwrap();
                offsets.push((bytes.offset() as u32, size));
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

// --- Sync: mixed read/write u8 ---

fn bench_sync_read_write_u8(c: &mut Criterion) {
  c.bench_function("sync_read_write_u8", |b| {
    b.iter_batched(
      || {
        let arena = make_sync_arena(1 << 20, Freelist::None);
        // Allocate some bytes first
        for _ in 0..100 {
          let _ = arena.alloc_bytes(64).unwrap();
        }
        arena
      },
      |arena| {
        // Write then read u8 values
        for i in 0..1000u32 {
          let offset = arena.data_offset() + (i as usize % 100) * 64;
          let _ = arena.get_u8(offset);
        }
      },
      BatchSize::SmallInput,
    );
  });
}

// --- Sync: alloc_aligned_bytes ---

fn bench_sync_alloc_aligned(c: &mut Criterion) {
  let mut group = c.benchmark_group("sync_alloc_aligned");
  for &size in &[0u32, 64, 256] {
    group.bench_with_input(BenchmarkId::from_parameter(size), &size, |b, &size| {
      b.iter_batched(
        || make_sync_arena(256 << 20, Freelist::None),
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
  // Single-thread fast path
  bench_sync_alloc_bytes_no_contention,
  bench_unsync_alloc_bytes,
  bench_sync_alloc_aligned,
  bench_sync_read_write_u8,
  // Contention
  bench_sync_alloc_bytes_contended,
  bench_sync_alloc_bytes_high_contention,
  // Freelist
  bench_sync_alloc_dealloc_optimistic,
  bench_sync_alloc_dealloc_pessimistic,
  bench_unsync_alloc_dealloc,
  // Freelist + contention
  bench_sync_alloc_dealloc_contended,
);
criterion_main!(benches);
