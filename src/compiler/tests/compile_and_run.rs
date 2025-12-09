use simple_compiler::CompilerPipeline;
use simple_loader::ModuleLoader;

/// Helper to compile and run a simple program
fn compile_and_run(src: &str) -> i32 {
    let dir = tempfile::tempdir().unwrap();
    let src_path = dir.path().join("main.simple");
    let out_path = dir.path().join("main.smf");

    std::fs::write(&src_path, src).unwrap();

    let mut compiler = CompilerPipeline::new().unwrap();
    compiler.compile(&src_path, &out_path).unwrap();

    let loader = ModuleLoader::new();
    let module = loader.load(&out_path).unwrap();

    type MainFn = extern "C" fn() -> i32;
    let main: MainFn = module.entry_point().expect("main symbol");
    main()
}

#[test]
fn compile_and_run_main() {
    assert_eq!(compile_and_run("main = 0"), 0);
}

#[test]
fn compile_integer_literal() {
    assert_eq!(compile_and_run("main = 42"), 42);
}

#[test]
fn compile_negative_integer() {
    assert_eq!(compile_and_run("main = -5"), -5);
}

#[test]
fn compile_addition() {
    assert_eq!(compile_and_run("main = 10 + 32"), 42);
}

#[test]
fn compile_subtraction() {
    assert_eq!(compile_and_run("main = 50 - 8"), 42);
}

#[test]
fn compile_multiplication() {
    assert_eq!(compile_and_run("main = 6 * 7"), 42);
}

#[test]
fn compile_division() {
    assert_eq!(compile_and_run("main = 84 / 2"), 42);
}

#[test]
fn compile_modulo() {
    assert_eq!(compile_and_run("main = 47 % 5"), 2);
}

#[test]
fn compile_comparison_lt() {
    assert_eq!(compile_and_run("main = if 1 < 2: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 2 < 1: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_gt() {
    assert_eq!(compile_and_run("main = if 2 > 1: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 1 > 2: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_lte() {
    assert_eq!(compile_and_run("main = if 1 <= 1: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 2 <= 1: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_gte() {
    assert_eq!(compile_and_run("main = if 2 >= 2: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 1 >= 2: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_eq() {
    assert_eq!(compile_and_run("main = if 42 == 42: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 42 == 43: 1 else: 0"), 0);
}

#[test]
fn compile_comparison_ne() {
    assert_eq!(compile_and_run("main = if 42 != 43: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if 42 != 42: 1 else: 0"), 0);
}

#[test]
fn compile_logical_and() {
    assert_eq!(compile_and_run("main = if true and true: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if true and false: 1 else: 0"), 0);
}

#[test]
fn compile_logical_or() {
    assert_eq!(compile_and_run("main = if false or true: 1 else: 0"), 1);
    assert_eq!(compile_and_run("main = if false or false: 1 else: 0"), 0);
}

#[test]
fn compile_let_binding() {
    assert_eq!(compile_and_run("let x = 42\nmain = x"), 42);
}

#[test]
fn compile_multiple_lets() {
    assert_eq!(compile_and_run("let a = 10\nlet b = 32\nmain = a + b"), 42);
}

#[test]
fn compile_function_definition() {
    assert_eq!(compile_and_run(r#"
fn add(a, b):
    return a + b
main = add(10, 32)
"#), 42);
}

#[test]
fn compile_nested_arithmetic() {
    assert_eq!(compile_and_run("main = (10 + 20) * 2 - 18"), 42);
}

#[test]
fn compile_boolean_true() {
    assert_eq!(compile_and_run("main = if true: 42 else: 0"), 42);
}

#[test]
fn compile_boolean_false() {
    assert_eq!(compile_and_run("main = if false: 0 else: 42"), 42);
}
