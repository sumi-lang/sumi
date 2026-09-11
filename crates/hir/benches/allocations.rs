//! Allocation counts, deliberately separate from wall-time benchmarks so the
//! instrumentation cannot distort them. Counts include successful realloc calls
//! and their full requested sizes; bytes are allocation traffic, not peak RSS.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use sumi_hir::{Ty, analyze};

#[path = "support/graphs.rs"]
mod graphs;
#[path = "support/programs.rs"]
mod programs;
#[allow(dead_code)]
#[path = "../src/solver.rs"]
mod solver;
#[allow(dead_code)]
#[path = "../src/typing.rs"]
mod typing;

struct Counting;
static CALLS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);

fn record(pointer: *mut u8, bytes: usize) {
    if !pointer.is_null() {
        CALLS.fetch_add(1, Relaxed);
        BYTES.fetch_add(bytes, Relaxed);
    }
}

// SAFETY: Every allocation/deallocation is delegated unchanged to System.
// Instrumentation uses only nonallocating atomics. No production crate uses
// this allocator; this single-threaded executable measures one phase at a time.
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
    for shape in graphs::SHAPES {
        for size in graphs::SIZES {
            let mut graph = graphs::build(shape, size);
            measure("solve", shape, size, || graph.context.solve());
            graphs::validate(shape, &graph);
            measure("replay-context", shape, size, || graph.context.replay());
            let (graph, _) = measure("build-solve-replay", shape, size, || {
                let mut graph = graphs::build(shape, size);
                graph.context.solve();
                let replay = graph.context.replay();
                (graph, replay)
            });
            graphs::validate(shape, &graph);
        }
    }
    for shape in programs::SHAPES {
        for size in programs::SIZES {
            let parsed = programs::parse(&programs::source(shape, size));
            let analysis = measure("analyze", shape, size, || analyze(parsed));
            programs::validate(shape, size, &analysis);
        }
    }
}
