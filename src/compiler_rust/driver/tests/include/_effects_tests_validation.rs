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
