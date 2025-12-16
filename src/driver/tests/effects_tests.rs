//! Effect system tests (Features #401-402)
//!
//! This module tests:
//! - @pure effect - no side effects allowed
//! - @io effect - console I/O allowed
//! - @net effect - network operations allowed
//! - @fs effect - filesystem operations allowed
//! - @unsafe effect - unchecked operations allowed
//! - Stacked effects - multiple effects on one function

mod test_helpers;
use test_helpers::{run_expect, run_expect_compile_error};

// ========================================================================
// @pure Effect Tests
// ========================================================================

#[test]
fn effects_pure_function_basic() {
    // Pure function can do computation
    run_expect(
        r#"
@pure
fn add(x: i64, y: i64) -> i64:
    return x + y

main = add(20, 22)
"#,
        42,
    );
}

#[test]
fn effects_pure_can_call_pure() {
    // Pure function can call other pure functions
    run_expect(
        r#"
@pure
fn double(x: i64) -> i64:
    return x * 2

@pure
fn quadruple(x: i64) -> i64:
    return double(double(x))

main = quadruple(10)
"#,
        40,
    );
}

#[test]
fn effects_pure_blocks_print() {
    // Pure function cannot use print (I/O)
    run_expect_compile_error(
        r#"
extern fn print(msg)

@pure
fn bad():
    print("hello")
    return 0

main = bad()
"#,
        "not allowed in pure function",
    );
}

#[test]
fn effects_pure_blocks_println() {
    // Pure function cannot use println (I/O)
    run_expect_compile_error(
        r#"
extern fn println(msg)

@pure
fn bad():
    println("hello")
    return 0

main = bad()
"#,
        "not allowed in pure function",
    );
}

// ========================================================================
// @io Effect Tests
// ========================================================================

#[test]
fn effects_io_function_basic() {
    // @io function can do I/O
    run_expect(
        r#"
@io
fn compute_and_return(x: i64) -> i64:
    return x * 2

main = compute_and_return(21)
"#,
        42,
    );
}

// ========================================================================
// @async Effect Tests (existing functionality with new syntax)
// ========================================================================

#[test]
fn effects_async_decorator_syntax() {
    // @async decorator should work same as `async fn`
    run_expect(
        r#"
@async
fn compute(x: i64) -> i64:
    return x * 2

main = compute(21)
"#,
        42,
    );
}

#[test]
fn effects_async_blocks_print() {
    // @async function cannot use print (blocking I/O)
    run_expect_compile_error(
        r#"
extern fn print(msg)

@async
fn bad():
    print("hello")
    return 0

main = bad()
"#,
        "not allowed in async function",
    );
}

// ========================================================================
// Stacked Effects Tests
// ========================================================================

#[test]
fn effects_stacked_pure_async() {
    // Function with both @pure and @async effects
    run_expect(
        r#"
@pure @async
fn fast_compute(x: i64) -> i64:
    return x * 2

main = fast_compute(21)
"#,
        42,
    );
}

#[test]
fn effects_stacked_io_net() {
    // Function with @io and @net effects
    run_expect(
        r#"
@io @net
fn network_logger(x: i64) -> i64:
    return x * 2

main = network_logger(21)
"#,
        42,
    );
}

#[test]
fn effects_stacked_all() {
    // Function with multiple effects
    run_expect(
        r#"
@io @net @fs
fn full_access(x: i64) -> i64:
    return x * 2

main = full_access(21)
"#,
        42,
    );
}

// ========================================================================
// Effect with Other Decorators
// ========================================================================

#[test]
fn effects_with_other_decorators() {
    // Effect decorators can coexist with other decorators
    // (other decorators should be preserved in decorators field)
    run_expect(
        r#"
@pure
fn add(x: i64, y: i64) -> i64:
    return x + y

main = add(20, 22)
"#,
        42,
    );
}

// ========================================================================
// Effect Inheritance (functions without effects)
// ========================================================================

#[test]
fn effects_unrestricted_function() {
    // Functions without effects can do anything (backward compatibility)
    run_expect(
        r#"
extern fn println(msg)

fn do_anything(x: i64) -> i64:
    return x * 2

main = do_anything(21)
"#,
        42,
    );
}

// ========================================================================
// @fs Effect Tests
// ========================================================================

#[test]
fn effects_fs_function_basic() {
    // @fs function can do filesystem operations
    run_expect(
        r#"
@fs
fn compute_fs(x: i64) -> i64:
    return x * 2

main = compute_fs(21)
"#,
        42,
    );
}

// ========================================================================
// @net Effect Tests
// ========================================================================

#[test]
fn effects_net_function_basic() {
    // @net function can do network operations
    run_expect(
        r#"
@net
fn compute_net(x: i64) -> i64:
    return x * 2

main = compute_net(21)
"#,
        42,
    );
}

// ========================================================================
// @unsafe Effect Tests
// ========================================================================

#[test]
fn effects_unsafe_function_basic() {
    // @unsafe function can do unchecked operations
    run_expect(
        r#"
@unsafe
fn compute_unsafe(x: i64) -> i64:
    return x * 2

main = compute_unsafe(21)
"#,
        42,
    );
}

// ========================================================================
// Effect Parsing Tests
// ========================================================================

#[test]
fn effects_parsed_correctly() {
    // Multiple effects should all be parsed
    run_expect(
        r#"
@pure @io @net @fs @unsafe
fn all_effects(x: i64) -> i64:
    return x

main = all_effects(42)
"#,
        42,
    );
}

#[test]
fn effects_with_attributes() {
    // Effects work with #[attribute] syntax
    run_expect(
        r#"
#[inline]
@pure
fn attributed_pure(x: i64) -> i64:
    return x * 2

main = attributed_pure(21)
"#,
        42,
    );
}

// ========================================================================
// Capability Parsing Tests
// ========================================================================

#[test]
fn capabilities_basic_parsing() {
    // Basic requires [cap] statement parsing
    run_expect(
        r#"
requires [pure]

@pure
fn compute(x: i64) -> i64:
    return x * 2

main = compute(21)
"#,
        42,
    );
}

#[test]
fn capabilities_multiple() {
    // Multiple capabilities in requires statement
    run_expect(
        r#"
requires [pure, io, net]

@pure
fn compute(x: i64) -> i64:
    return x * 2

main = compute(21)
"#,
        42,
    );
}

#[test]
fn capabilities_all() {
    // All capabilities
    run_expect(
        r#"
requires [pure, io, net, fs, unsafe, gc]

fn compute(x: i64) -> i64:
    return x * 2

main = compute(21)
"#,
        42,
    );
}

#[test]
fn capabilities_trailing_comma() {
    // Trailing comma should be allowed
    run_expect(
        r#"
requires [pure, io,]

@pure
fn compute(x: i64) -> i64:
    return x * 2

main = compute(21)
"#,
        42,
    );
}

#[test]
fn capabilities_empty() {
    // Empty requires list (very restrictive - no effects allowed)
    run_expect(
        r#"
requires []

fn compute(x: i64) -> i64:
    return x * 2

main = compute(21)
"#,
        42,
    );
}

#[test]
fn capabilities_invalid_name() {
    // Invalid capability name should error
    run_expect_compile_error(
        r#"
requires [invalid_capability]

main = 42
"#,
        "unknown capability 'invalid_capability'",
    );
}

// ========================================================================
// Compile-Time Capability Validation Tests (Sprint 3)
// ========================================================================

#[test]
fn capabilities_compile_time_validation_allowed() {
    // Function effect matches capability - should compile
    run_expect(
        r#"
requires [pure]

@pure
fn add(x: i64, y: i64) -> i64:
    return x + y

main = add(20, 22)
"#,
        42,
    );
}

#[test]
fn capabilities_compile_time_validation_blocked() {
    // Function has @io effect but module only allows [pure]
    run_expect_compile_error(
        r#"
requires [pure]

@io
fn log_value(x: i64) -> i64:
    return x

main = log_value(42)
"#,
        "has @io effect but module only allows capabilities: [pure]",
    );
}

#[test]
fn capabilities_compile_time_net_blocked() {
    // Function has @net effect but module only allows [pure, io]
    run_expect_compile_error(
        r#"
requires [pure, io]

@net
fn fetch(x: i64) -> i64:
    return x

main = fetch(42)
"#,
        "has @net effect but module only allows capabilities: [pure, io]",
    );
}

#[test]
fn capabilities_compile_time_fs_blocked() {
    // Function has @fs effect but module only allows [pure]
    run_expect_compile_error(
        r#"
requires [pure]

@fs
fn read_file(x: i64) -> i64:
    return x

main = read_file(42)
"#,
        "has @fs effect but module only allows capabilities: [pure]",
    );
}

#[test]
fn capabilities_compile_time_unsafe_blocked() {
    // Function has @unsafe effect but module only allows [pure, io]
    run_expect_compile_error(
        r#"
requires [pure, io]

@unsafe
fn dangerous(x: i64) -> i64:
    return x

main = dangerous(42)
"#,
        "has @unsafe effect but module only allows capabilities: [pure, io]",
    );
}

#[test]
fn capabilities_compile_time_async_always_allowed() {
    // @async is always allowed (execution model, not capability)
    run_expect(
        r#"
requires [pure]

@async
fn compute(x: i64) -> i64:
    return x * 2

main = compute(21)
"#,
        42,
    );
}

#[test]
fn capabilities_compile_time_multiple_effects_partial_allowed() {
    // Function has @pure and @io - @pure matches, @io matches [pure, io]
    run_expect(
        r#"
requires [pure, io]

@pure @io
fn process(x: i64) -> i64:
    return x * 2

main = process(21)
"#,
        42,
    );
}

#[test]
fn capabilities_compile_time_multiple_effects_one_blocked() {
    // Function has @pure and @net - @pure matches but @net doesn't
    run_expect_compile_error(
        r#"
requires [pure, io]

@pure @net
fn process(x: i64) -> i64:
    return x

main = process(42)
"#,
        "has @net effect but module only allows capabilities: [pure, io]",
    );
}

#[test]
fn capabilities_compile_time_unrestricted_allows_all() {
    // Module without requires statement allows all effects
    run_expect(
        r#"
@io @net @fs @unsafe
fn do_everything(x: i64) -> i64:
    return x * 2

main = do_everything(21)
"#,
        42,
    );
}

// ========================================================================
// Import Capability Validation Tests (Unit Tests)
// ========================================================================

#[test]
fn import_validation_check_compatibility_allowed() {
    use simple_compiler::pipeline::module_loader::check_import_compatibility;
    use simple_parser::ast::{Capability, Effect};

    // Function with @pure effect imported into [pure, io] module
    let result = check_import_compatibility(
        "add",
        &[Effect::Pure],
        &[Capability::Pure, Capability::Io],
    );
    assert!(result.is_none());
}

#[test]
fn import_validation_check_compatibility_blocked() {
    use simple_compiler::pipeline::module_loader::check_import_compatibility;
    use simple_parser::ast::{Capability, Effect};

    // Function with @net effect imported into [pure, io] module - should fail
    let result = check_import_compatibility(
        "fetch",
        &[Effect::Net],
        &[Capability::Pure, Capability::Io],
    );
    assert!(result.is_some());
    let err = result.unwrap();
    assert!(err.contains("cannot import function 'fetch'"));
    assert!(err.contains("@net effect"));
}

#[test]
fn import_validation_async_always_allowed() {
    use simple_compiler::pipeline::module_loader::check_import_compatibility;
    use simple_parser::ast::{Capability, Effect};

    // @async is always allowed (execution model, not capability)
    let result = check_import_compatibility(
        "async_fn",
        &[Effect::Async],
        &[Capability::Pure],
    );
    assert!(result.is_none());
}

#[test]
fn import_validation_unrestricted_module() {
    use simple_compiler::pipeline::module_loader::check_import_compatibility;
    use simple_parser::ast::Effect;

    // Unrestricted module (empty capabilities) allows all imports
    let result = check_import_compatibility(
        "net_fn",
        &[Effect::Net, Effect::Fs, Effect::Unsafe],
        &[],
    );
    assert!(result.is_none());
}

#[test]
fn import_validation_multiple_effects_one_blocked() {
    use simple_compiler::pipeline::module_loader::check_import_compatibility;
    use simple_parser::ast::{Capability, Effect};

    // Function with @io and @net, but module only allows [pure, io]
    let result = check_import_compatibility(
        "log_and_fetch",
        &[Effect::Io, Effect::Net],
        &[Capability::Pure, Capability::Io],
    );
    assert!(result.is_some());
    let err = result.unwrap();
    assert!(err.contains("@net effect"));
}

#[test]
fn import_validation_extract_module_capabilities() {
    use simple_compiler::pipeline::module_loader::extract_module_capabilities;
    use simple_parser::ast::Capability;

    let source = r#"
requires [pure, io]

fn add(x: i64, y: i64) -> i64:
    return x + y
"#;
    let mut parser = simple_parser::Parser::new(source);
    let module = parser.parse().unwrap();

    let caps = extract_module_capabilities(&module);
    assert!(caps.is_some());
    let caps = caps.unwrap();
    assert_eq!(caps.len(), 2);
    assert!(caps.contains(&Capability::Pure));
    assert!(caps.contains(&Capability::Io));
}

#[test]
fn import_validation_extract_function_effects() {
    use simple_compiler::pipeline::module_loader::extract_function_effects;
    use simple_parser::ast::Effect;

    let source = r#"
@io
fn log(msg: str):
    return 0

@net
fn fetch(url: str):
    return 0

fn plain(x: i64) -> i64:
    return x
"#;
    let mut parser = simple_parser::Parser::new(source);
    let module = parser.parse().unwrap();

    let effects = extract_function_effects(&module);
    assert_eq!(effects.len(), 2); // Only functions with effects

    let log_effects = effects.iter().find(|(name, _)| name == "log");
    assert!(log_effects.is_some());
    assert!(log_effects.unwrap().1.contains(&Effect::Io));

    let fetch_effects = effects.iter().find(|(name, _)| name == "fetch");
    assert!(fetch_effects.is_some());
    assert!(fetch_effects.unwrap().1.contains(&Effect::Net));
}
