//! Allocation counts, kept separate from wall-time benchmarks so instrumentation doesn't distort
//! them. Counts include successful reallocs; bytes are requested-size traffic, not peak RSS.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use sumi_hir::analyze;

#[path = "support/programs.rs"]
mod programs;

struct Counting;
static CALLS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);

fn record(pointer: *mut u8, bytes: usize) {
    if !pointer.is_null() {
        CALLS.fetch_add(1, Relaxed);
        BYTES.fetch_add(bytes, Relaxed);
    }
}

// SAFETY: allocation and deallocation are delegated unchanged to System; only nonallocating atomics
// record counts.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc(layout) };
        record(pointer, layout.size());
        pointer
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc_zeroed(layout) };
        record(pointer, layout.size());
        pointer
    }
    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let pointer = unsafe { System.realloc(pointer, layout, size) };
        record(pointer, size);
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

fn measure<T>(phase: &str, shape: &str, size: usize, run: impl FnOnce() -> T) -> T {
    let calls = CALLS.load(Relaxed);
    let bytes = BYTES.load(Relaxed);
    let result = run();
    std::hint::black_box(&result);
    let calls = CALLS.load(Relaxed) - calls;
    let bytes = BYTES.load(Relaxed) - bytes;
    println!("{phase},{shape},{size},{calls},{bytes}");
    result
}

fn main() {
    println!("phase,shape,size,allocation_calls,requested_bytes");
    for shape in programs::SHAPES {
        for size in programs::SIZES {
            let parsed = programs::parse(&programs::source(shape, size));
            let analysis = measure("analyze", shape, size, || analyze(parsed));
            programs::validate(shape, size, &analysis);
        }
    }
}
