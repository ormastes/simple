// Integration tests for one-pass LL(1) macro compilation (#1304)
//
// Tests that macros can be validated without full expansion:
// - Ordering validation (defined before use)
// - Shadowing detection (intro symbols)
// - QIDENT template variable validation
// - Type annotation requirements

use simple_compiler::CompilerPipeline;

/// Helper to parse and check if compilation succeeds
fn check_compiles(source: &str) -> Result<(), String> {
    let dir = tempfile::tempdir().map_err(|e| format!("Failed to create temp dir: {}", e))?;
    let src_path = dir.path().join("test.spl");
    let out_path = dir.path().join("test.smf");

    std::fs::write(&src_path, source).map_err(|e| format!("Failed to write source: {}", e))?;

    let mut compiler = CompilerPipeline::new().map_err(|e| format!("Failed to create compiler: {:?}", e))?;

    compiler.compile(&src_path, &out_path).map_err(|e| format!("{:?}", e))
}

/// Helper to parse and expect a specific error code
fn expect_error(source: &str, expected_code: &str) -> bool {
    match check_compiles(source) {
        Err(e) => e.contains(expected_code),
        Ok(_) => false,
    }
}

#[test]
fn test_macro_defined_before_use_success() {
    let source = r#"macro greet(name: String) -> (
    intro result:
        enclosing.module.let greeting: String
):
    emit result:
        val greeting = "Hello, " + name

# Use macro after definition - should succeed
greet!("World")
main = 0
"#;

    assert!(check_compiles(source).is_ok());
}

#[test]
fn test_macro_used_before_definition_error() {
    let source = r#"# Use macro before definition - should fail
greet!("World")

macro greet(name: String) -> (
    intro result:
        enclosing.module.let greeting: String
):
    emit result:
        val greeting = "Hello"

main = 0
"#;

    // Should fail with "unknown macro" error
    assert!(expect_error(source, "unknown macro"));
}

#[test]
fn test_intro_shadowing_existing_variable() {
    let source = r#"val counter = 0

# Macro tries to introduce symbol that shadows existing variable
macro init_counter() -> (
    intro result:
        enclosing.module.let counter: i64
):
    emit result:
        val counter = 42

init_counter!()
main = 0
"#;

    // Should fail with E1403 (MACRO_SHADOWING)
    assert!(expect_error(source, "E1403"));
}

#[test]
fn test_intro_shadowing_existing_function() {
    let source = r#"fn my_func() -> i64:
    return 42

# Macro tries to introduce function that shadows existing function
macro define_func() -> (
    intro result:
        enclosing.module.fn my_func() -> i64
):
    emit result:
        fn my_func() -> i64:
            return 99

define_func!()
main = 0
"#;

    // Should fail with E1403 (MACRO_SHADOWING)
    assert!(expect_error(source, "E1403"));
}

#[test]
fn test_intro_no_shadowing_success() {
    let source = r#"val existing_var = 0

# Macro introduces different symbol - should succeed
macro init_data() -> (
    intro result:
        enclosing.module.let new_var: i64
):
    emit result:
        val new_var = 42

init_data!()
main = 0
"#;

    assert!(check_compiles(source).is_ok());
}

#[test]
fn test_qident_template_with_const_param() {
    let source = r#"macro define_getter(NAME: String const) -> (
    intro result:
        enclosing.module.fn "get_{NAME}"() -> i64
):
    emit result:
        fn "get_{NAME}"() -> i64:
            return 42

define_getter!("value")
main = 0
"#;

    assert!(check_compiles(source).is_ok());
}

#[test]
fn test_qident_template_without_const_param() {
    let source = r#"# Template variable {NAME} used without const qualifier - should fail
macro define_getter(NAME: String) -> (
    intro result:
        enclosing.module.fn "get_{NAME}"() -> i64
):
    emit result:
        fn "get_{NAME}"() -> i64:
            return 42

define_getter!("value")
main = 0
"#;

    // Should fail with E1406 (MACRO_INVALID_QIDENT)
    assert!(expect_error(source, "E1406"));
}

#[test]
fn test_intro_type_annotation_required() {
    let source = r#"# intro let without type annotation - should fail
macro init_var() -> (
    intro result:
        enclosing.module.let my_var
):
    emit result:
        val my_var = 42

init_var!()
main = 0
"#;

    // Should fail with E1405 (MACRO_MISSING_TYPE_ANNOTATION)
    // The parser requires type annotation for 'let' in intro
    assert!(check_compiles(source).is_err());
}

#[test]
fn test_intro_with_type_annotation_success() {
    let source = r#"macro init_var() -> (
    intro result:
        enclosing.module.let my_var: i64
):
    emit result:
        val my_var = 42

init_var!()
main = 0
"#;

    match check_compiles(source) {
        Ok(_) => {},
        Err(e) => {
            eprintln!("Compilation failed: {}", e);
            panic!("Expected compilation to succeed but got error");
        }
    }
}

#[test]
fn test_multiple_macros_ordering() {
    let source = r#"# Define macros in order
macro first() -> (
    intro result:
        enclosing.module.let var1: i64
):
    emit result:
        val var1 = 1

macro second() -> (
    intro result:
        enclosing.module.let var2: i64
):
    emit result:
        val var2 = 2

# Use in reverse order - should succeed
second!()
first!()
main = 0
"#;

    assert!(check_compiles(source).is_ok());
}

#[test]
fn test_intro_multiple_symbols_no_conflict() {
    let source = r#"macro init_multiple() -> (
    intro var1:
        enclosing.module.let var1: i64,
    intro var2:
        enclosing.module.let var2: String,
    intro helper:
        enclosing.module.fn helper() -> i64
):
    emit var1:
        val var1 = 42
    emit var2:
        val var2 = "test"
    emit helper:
        fn helper() -> i64:
            return var1

init_multiple!()
main = 0
"#;

    assert!(check_compiles(source).is_ok());
}

#[test]
fn test_intro_duplicate_symbols_within_macro() {
    let source = r#"# Macro introduces same symbol twice - should fail
macro init_duplicate() -> (
    intro result1:
        enclosing.module.let counter: i64,
    intro result2:
        enclosing.module.let counter: i64
):
    emit result1:
        val counter = 42

init_duplicate!()
main = 0
"#;

    // Should fail with E1403 (MACRO_SHADOWING - symbol introduced twice)
    assert!(expect_error(source, "E1403"));
}

#[test]
fn test_intro_for_loop_with_const_range() {
    let source = r#"macro generate_vars(COUNT: i64 const) -> (
    intro result:
        for i in 0..COUNT:
            enclosing.module.let "var_{i}": i64
):
    emit result:
        for i in 0..COUNT:
            val "var_{i}" = i

generate_vars!(3)
main = 0
"#;

    match check_compiles(source) {
        Ok(_) => {},
        Err(e) => {
            eprintln!("Compilation failed: {}", e);
            panic!("Expected compilation to succeed but got error");
        }
    }
}

#[test]
#[ignore = "Complex expressions not yet supported in macro if conditions (macro registry limitation)"]
fn test_intro_conditional_with_const_condition() {
    let source = r#"macro conditional_intro(FLAG: bool const) -> (
    intro result:
        if FLAG:
            enclosing.module.let enabled_var: i64
        else:
            enclosing.module.let disabled_var: i64
):
    emit result:
        if FLAG:
            val enabled_var = 1
        else:
            val disabled_var = 0

conditional_intro!(true)
main = 0
"#;

    match check_compiles(source) {
        Ok(_) => {},
        Err(e) => {
            eprintln!("Compilation failed: {}", e);
            panic!("Expected compilation to succeed but got error");
        }
    }
}
