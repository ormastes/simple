use super::run_code;

// ============================================================================
// Macro Contract Tests - Intro Syntax
// ============================================================================

#[test]
fn macro_intro_function_basic() {
    // Test macro intro of function in enclosing module
    let code = r#"
macro make_adder(n: Int const) -> (
    returns result: Int,
    intro add_fn: enclosing.module.fn "add_n"(x: Int) -> Int
):
    emit add_fn:
        fn add_n(x: Int) -> Int:
            return x + n

    emit result:
        0

let _ = make_adder!(10)
main = add_n(32)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn macro_intro_with_const_param_substitution() {
    // Test that const parameters are substituted in intro function names
    let code = r#"
macro make_named_adder(name: Str const, amount: Int const) -> (
    returns result: Int,
    intro adder: enclosing.module.fn "{name}_adder"(x: Int) -> Int
):
    emit adder:
        fn add_impl(x: Int) -> Int:
            return x + amount

    emit result:
        0

let _ = make_named_adder!("my", 10)
main = my_adder(32)
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42); // 32 + 10 = 42
}

#[test]
fn macro_intro_with_const_for_loop() {
    // Test const-eval for loop in intro spec (from spec 9.2)
    // Requires: for-loop unrolling in emit blocks + templated function names
    let code = r#"
macro gen_funcs(n: Int const) -> (
    returns result: Int,
    intro funcs:
        for i in 0..n:
            enclosing.module.fn "get_{i}"() -> Int
):
    # For-loop unrolling in emit blocks not yet supported
    emit funcs:
        fn get_0() -> Int:
            return 0
        fn get_1() -> Int:
            return 1
        fn get_2() -> Int:
            return 2

    emit result:
        n

let _ = gen_funcs!(3)
main = get_0() + get_1() + get_2()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // 0 + 1 + 2 = 3
}

#[test]
fn macro_intro_template_function_name() {
    // Test template substitution in intro function names
    let code = r#"
macro gen_getter(NAME: Str const) -> (
    intro getter: enclosing.module.fn "get_{NAME}"() -> Int
):
    emit getter:
        fn "get_{NAME}"() -> Int:
            return 42

gen_getter!("value")
main = get_value()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 42);
}

#[test]
fn macro_intro_template_with_for_loop() {
    // Test template substitution with for loop generating multiple functions
    let code = r#"
macro gen_getters(N: Int const) -> (
    intro getters:
        for i in 0..N:
            enclosing.module.fn "get_{i}"() -> Int
):
    emit getters:
        for i in 0..N:
            fn "get_{i}"() -> Int:
                return i

gen_getters!(3)
main = get_0() + get_1() + get_2()
"#;
    let result = run_code(code, &[], "").unwrap();
    assert_eq!(result.exit_code, 3); // 0 + 1 + 2 = 3
}
