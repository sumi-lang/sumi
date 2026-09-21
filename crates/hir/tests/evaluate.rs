#[path = "../benches/support/entry.rs"]
mod entry;

use sumi_frontend::parse_source;
use sumi_hir::{FunctionId, Value, analyze};

#[test]
fn entry_values_and_fallbacks_match_the_machine() {
    for &shape in entry::SHAPES {
        for &width in entry::WIDTHS {
            let analysis = analyze(parse_source(entry::source(shape, width).into()).unwrap());
            entry::validate(shape, &analysis);
            sumi_test::check::run(analysis.program().unwrap());
        }
    }
}

#[test]
fn evaluation_and_machine_construction_reject_the_same_invalid_calls() {
    for &shape in entry::SHAPES {
        let analysis = analyze(parse_source(entry::source(shape, 0).into()).unwrap());
        let program = analysis.program().unwrap();
        let function = program.function_named("entry").unwrap();
        for (function, args, message) in [
            (function, vec![], "arguments must match the signature"),
            (
                function,
                vec![Value::Int(1.into())],
                "arguments must match the signature",
            ),
            (
                function,
                vec![Value::Unit],
                "arguments must match the signature",
            ),
            (
                function,
                vec![Value::Bool(true); 2],
                "arguments must match the signature",
            ),
            (
                FunctionId::new(analysis.functions().len()),
                vec![Value::Bool(true)],
                "index out of bounds",
            ),
        ] {
            for evaluate in [false, true] {
                let panic = std::panic::catch_unwind(|| {
                    if evaluate {
                        program.evaluate(function, &args);
                    } else {
                        program.machine(function, &args);
                    }
                })
                .expect_err("invalid call must panic before producing a value");
                let text = panic
                    .downcast_ref::<String>()
                    .map(String::as_str)
                    .or_else(|| panic.downcast_ref::<&str>().copied())
                    .unwrap();
                assert!(text.contains(message), "{shape}: {text}");
            }
        }
    }
}
