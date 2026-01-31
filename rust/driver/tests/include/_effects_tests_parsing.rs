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

