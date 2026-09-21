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
