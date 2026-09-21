//! Allocation traffic and peak additional live requested bytes, separate from wall-time benchmarks.
//! Counts include successful reallocations; neither size metric is RSS.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use sumi_hir::analyze;

#[path = "support/programs.rs"]
mod programs;

#[path = "support/workloads.rs"]
mod workloads;

#[path = "support/deep.rs"]
mod deep;

#[path = "support/recursion.rs"]
mod recursion;

#[path = "support/slots.rs"]
mod slots;

#[path = "support/recursion_forms.rs"]
mod forms;

#[path = "support/entry.rs"]
mod entry;

struct Counting;
static CALLS: AtomicUsize = AtomicUsize::new(0);
static BYTES: AtomicUsize = AtomicUsize::new(0);
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

fn record(pointer: *mut u8, bytes: usize) {
    if !pointer.is_null() {
        CALLS.fetch_add(1, Relaxed);
        BYTES.fetch_add(bytes, Relaxed);
        let live = LIVE.fetch_add(bytes, Relaxed) + bytes;
        PEAK.fetch_max(live, Relaxed);
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
        if !pointer.is_null() {
            LIVE.fetch_sub(layout.size(), Relaxed);
        }
        record(pointer, size);
        pointer
    }
    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) };
        LIVE.fetch_sub(layout.size(), Relaxed);
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

fn measure<T>(phase: &str, shape: &str, size: usize, run: impl FnOnce() -> T) -> T {
    let calls = CALLS.load(Relaxed);
    let bytes = BYTES.load(Relaxed);
    let live = LIVE.load(Relaxed);
    PEAK.store(live, Relaxed);
    let result = run();
    std::hint::black_box(&result);
    let calls = CALLS.load(Relaxed) - calls;
    let bytes = BYTES.load(Relaxed) - bytes;
    let peak = PEAK.load(Relaxed) - live;
    println!("{phase},{shape},{size},{calls},{bytes},{peak}");
    result
}

fn main() {
    println!("phase,shape,size,allocation_calls,requested_bytes,peak_extra_live_bytes");
    if std::env::args().any(|arg| arg == "--entry") {
        for &shape in entry::SHAPES {
            for &width in entry::WIDTHS {
                let source = entry::source(shape, width);
                let parsed = workloads::parse(&source);
                let analysis = measure("analyze", shape, width, || analyze(parsed));
                entry::validate(shape, &analysis);
                let program = analysis.program().unwrap();
                let function = program.function_named("entry").unwrap();
                measure("evaluate", shape, width, || {
                    program.evaluate(function, &[sumi_hir::Value::Bool(true)])
                });
            }
        }
        return;
    }
    if std::env::args().any(|arg| arg == "--forms") {
        for &shape in forms::SHAPES {
            for &size in forms::SIZES {
                let source = forms::source(shape, size);
                let parsed = workloads::parse(&source);
                let analysis = measure("analyze", shape, size, || analyze(parsed));
                forms::validate(shape, size, &analysis);
                measure("execute", shape, size, || forms::evaluate(&analysis));
                let program = analysis.program().unwrap();
                let main = program.function_named("main").unwrap();
                let mut machine = program.machine(main, &[]);
                while machine.step().is_none() {}
                eprintln!(
                    "{shape},{size},source_bytes={},nodes={},steps={},depth={}",
                    source.len(),
                    analysis.graph().nodes().len(),
                    machine.steps(),
                    machine.max_depth()
                );
            }
        }
        return;
    }
    if std::env::args().any(|arg| arg == "--slots") {
        for &shape in slots::SHAPES {
            for &(width, depth) in slots::SIZES {
                let analysis = analyze(workloads::parse(&slots::source(shape, width, depth)));
                let name = format!("{shape}-{depth}");
                measure("cold", &name, width, || slots::evaluate(&analysis));
                slots::validate(&analysis, width, depth);
                measure("warm", &name, width, || slots::evaluate(&analysis));
            }
        }
        return;
    }
    if std::env::args().any(|arg| arg == "--lowering") {
        for shape in [
            "locals",
            "scoped-mutation",
            "wide-mutation",
            "narrow-mutation",
            "nested-mutation",
            "expression-chain",
        ] {
            for size in programs::SIZES {
                let parsed = programs::parse(&programs::source(shape, size));
                let analysis = measure("analyze", shape, size, || analyze(parsed));
                programs::validate(shape, size, &analysis);
            }
        }
        return;
    }
    if std::env::args().any(|arg| arg == "--recursion") {
        for &(shape, sizes) in recursion::CASES {
            for &size in sizes {
                recursion::checked(shape, size);
                let parsed = programs::parse(&recursion::source(shape, size));
                let analysis = measure("analyze", shape, size, || analyze(parsed));
                recursion::validate(shape, size, &analysis);
            }
        }
        return;
    }
    for &shape in deep::SHAPES {
        for &depth in deep::SIZES {
            let analysis = analyze(workloads::parse(&deep::source(shape, depth)));
            workloads::validate(&analysis, depth as i64 + 7);
            let program = analysis.program().unwrap();
            let main = program.function_named("main").unwrap();
            measure("execute", shape, depth, || program.evaluate(main, &[]));
            let mut machine = program.machine(main, &[]);
            while machine.step().is_none() {}
            eprintln!(
                "{shape},{depth},steps={},depth={}",
                machine.steps(),
                machine.max_depth()
            );
        }
    }
    for &(name, source, expected) in workloads::CASES {
        let parsed = measure("parse", name, source.len(), || workloads::parse(source));
        let analysis = measure("analyze", name, source.len(), || analyze(parsed));
        workloads::validate(&analysis, expected);
        let program = analysis.program().unwrap();
        let main = program.function_named("main").unwrap();
        measure("execute", name, source.len(), || {
            program.evaluate(main, &[])
        });
    }
    for shape in programs::SHAPES {
        for size in programs::SIZES {
            let parsed = programs::parse(&programs::source(shape, size));
            let analysis = measure("analyze", shape, size, || analyze(parsed));
            programs::validate(shape, size, &analysis);
        }
    }
}
