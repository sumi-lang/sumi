#[path = "../benches/support/recursion.rs"]
mod recursion;

#[path = "../benches/support/recursion_forms.rs"]
mod forms;

#[test]
fn recursive_shapes() {
    for &(shape, sizes) in recursion::CASES {
        recursion::checked(shape, sizes[0]);
    }
}

#[test]
fn recursive_forms_include_unrolled_remainders() {
    for &shape in forms::SHAPES {
        for &size in forms::SIZES.iter().chain(&[0, 1, 3, 4, 5, 17]) {
            let parsed = sumi_frontend::parse_source(forms::source(shape, size).into()).unwrap();
            forms::validate(shape, size, &sumi_hir::analyze(parsed));
        }
    }
}

#[test]
fn unit_returns_demand_recursion_but_discarded_calls_do_not() {
    for size in [0, 1, 17, 128] {
        for (shape, depth) in [
            ("known-unit", size + 2),
            ("unused-unit-call", 2),
            ("unused-int-call", 1),
        ] {
            let parsed = sumi_frontend::parse_source(forms::source(shape, size).into()).unwrap();
            let analysis = sumi_hir::analyze(parsed);
            let program = analysis.program().unwrap();
            let main = program.function_named("main").unwrap();
            let mut machine = program.machine(main, &[]);
            while machine.step().is_none() {}
            assert_eq!(machine.max_depth(), depth, "{shape}/{size}");
            assert_eq!(machine.outcome(), Some(&Ok(forms::expected(shape, size))));
            assert_eq!(program.evaluate(main, &[]), forms::expected(shape, size));
        }
    }
}
