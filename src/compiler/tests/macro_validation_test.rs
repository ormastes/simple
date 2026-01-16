// Integration tests for one-pass LL(1) macro compilation (#1304)
//
// Tests that macros can be validated without full expansion:
// - Ordering validation (defined before use)
// - Shadowing detection (intro symbols)
// - QIDENT template variable validation
// - Type annotation requirements

use simple_compiler::error::CompileError;
use simple_parser::Parser;

/// Helper to parse and check if compilation succeeds
fn check_compiles(source: &str) -> Result<(), CompileError> {
    let mut parser = Parser::new(source);
    let module = parser.parse().map_err(|e| CompileError::Parse(e.to_string()))?;
    simple_compiler::evaluate_module(&module.items).map(|_| ())
}

/// Helper to parse and expect a specific error code
fn expect_error(source: &str, expected_code: &str) -> bool {
    match check_compiles(source) {
        Err(e) => {
            let err_str = e.to_string();
            err_str.contains(expected_code)
        }
        Ok(_) => false,
    }
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_macro_defined_before_use_success() {
    let source = r#"
        macro greet(name):
            contract:
                intro: let greeting: str
            const_eval:
                pass
            emit result:
                let greeting = "Hello, " + name

        # Use macro after definition - should succeed
        greet!("World")
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_macro_used_before_definition_error() {
    let source = r#"
        # Use macro before definition - should fail with E1402
        greet!("World")

        macro greet(name):
            contract:
                intro: let greeting: str
            const_eval:
                pass
            emit result:
                let greeting = "Hello"

        main = 0
    "#;

    assert!(expect_error(source, "E1402"));
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_shadowing_existing_variable() {
    let source = r#"
        let counter = 0

        # Macro tries to introduce symbol that shadows existing variable
        macro init_counter():
            contract:
                intro: let counter: int
            const_eval:
                pass
            emit result:
                let counter = 42

        init_counter!()
        main = 0
    "#;

    // Should fail with E1403 (MACRO_SHADOWING)
    assert!(expect_error(source, "E1403"));
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_shadowing_existing_function() {
    let source = r#"
        fn my_func():
            return 42

        # Macro tries to introduce function that shadows existing function
        macro define_func():
            contract:
                intro: fn my_func() -> int
            const_eval:
                pass
            emit result:
                fn my_func():
                    return 99

        define_func!()
        main = 0
    "#;

    // Should fail with E1403 (MACRO_SHADOWING)
    assert!(expect_error(source, "E1403"));
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_no_shadowing_success() {
    let source = r#"
        let existing_var = 0

        # Macro introduces different symbol - should succeed
        macro init_data():
            contract:
                intro: let new_var: int
            const_eval:
                pass
            emit result:
                let new_var = 42

        init_data!()
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_qident_template_with_const_param() {
    let source = r#"
        macro define_getter(const NAME):
            contract:
                intro: fn get_{NAME}() -> int
            const_eval:
                pass
            emit result:
                fn get_{NAME}():
                    return 42

        define_getter!("value")
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_qident_template_without_const_param() {
    let source = r#"
        # Template variable {NAME} used without const qualifier - should fail
        macro define_getter(NAME):
            contract:
                intro: fn get_{NAME}() -> int
            const_eval:
                pass
            emit result:
                fn get_{NAME}():
                    return 42

        define_getter!("value")
        main = 0
    "#;

    // Should fail with E1406 (MACRO_INVALID_QIDENT)
    assert!(expect_error(source, "E1406"));
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_type_annotation_required() {
    let source = r#"
        # intro let without type annotation - should fail
        macro init_var():
            contract:
                intro: let my_var
            const_eval:
                pass
            emit result:
                let my_var = 42

        init_var!()
        main = 0
    "#;

    // Should fail with E1405 (MACRO_MISSING_TYPE_ANNOTATION)
    // Note: This would be caught by the parser, so we expect a parse error
    assert!(check_compiles(source).is_err());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_with_type_annotation_success() {
    let source = r#"
        macro init_var():
            contract:
                intro: let my_var: int
            const_eval:
                pass
            emit result:
                let my_var = 42

        init_var!()
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_multiple_macros_ordering() {
    let source = r#"
        # Define macros in order
        macro first():
            contract:
                intro: let var1: int
            emit result:
                let var1 = 1

        macro second():
            contract:
                intro: let var2: int
            emit result:
                let var2 = 2

        # Use in reverse order - should succeed
        second!()
        first!()
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_multiple_symbols_no_conflict() {
    let source = r#"
        macro init_multiple():
            contract:
                intro: let var1: int
                intro: let var2: str
                intro: fn helper() -> int
            const_eval:
                pass
            emit result:
                let var1 = 42
                let var2 = "test"
                fn helper():
                    return var1

        init_multiple!()
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_duplicate_symbols_within_macro() {
    let source = r#"
        # Macro introduces same symbol twice - should fail
        macro init_duplicate():
            contract:
                intro: let counter: int
                intro: let counter: int
            const_eval:
                pass
            emit result:
                let counter = 42

        init_duplicate!()
        main = 0
    "#;

    // Should fail with E1403 (MACRO_SHADOWING - symbol introduced twice)
    assert!(expect_error(source, "E1403"));
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_for_loop_with_const_range() {
    let source = r#"
        macro generate_vars(const COUNT):
            contract:
                intro for i in 0..COUNT:
                    let var_{i}: int
            const_eval:
                pass
            emit result:
                for i in 0..COUNT:
                    let var_{i} = i

        generate_vars!(3)
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}

#[test]
#[ignore = "Advanced macro syntax (intro/emit blocks) not implemented in parser"]
fn test_intro_conditional_with_const_condition() {
    let source = r#"
        macro conditional_intro(const FLAG):
            contract:
                intro if FLAG:
                    let enabled_var: int
                else:
                    let disabled_var: int
            const_eval:
                pass
            emit result:
                if FLAG:
                    let enabled_var = 1
                else:
                    let disabled_var = 0

        conditional_intro!(true)
        main = 0
    "#;

    assert!(check_compiles(source).is_ok());
}
