// ========================================================================
// Effect Propagation Tests (Sprint 3 - #882)
// ========================================================================

#[test]
fn effects_pure_cannot_call_io() {
    // Pure function cannot call a function with @io effect
    run_expect_compile_error(
        r#"
extern fn print(msg)

@io
fn log_value(x: i64) -> i64:
    print("logging")
    return x

@pure
fn compute(x: i64) -> i64:
    return log_value(x) * 2

main = compute(20)
"#,
        "pure function cannot call",
    );
}

#[test]
fn effects_pure_cannot_call_net() {
    // Pure function cannot call a function with @net effect
    run_expect_compile_error(
        r#"
@net
fn fetch_data() -> i64:
    return 42

@pure
fn process() -> i64:
    return fetch_data() * 2

main = process()
"#,
        "pure function cannot call",
    );
}

#[test]
fn effects_pure_cannot_call_fs() {
    // Pure function cannot call a function with @fs effect
    run_expect_compile_error(
        r#"
@fs
fn read_config() -> i64:
    return 42

@pure
fn get_value() -> i64:
    return read_config() + 10

main = get_value()
"#,
        "pure function cannot call",
    );
}

#[test]
fn effects_pure_cannot_call_unsafe() {
    // Pure function cannot call a function with @unsafe effect
    run_expect_compile_error(
        r#"
@unsafe
fn dangerous() -> i64:
    return 42

@pure
fn safe_wrapper() -> i64:
    return dangerous() + 1

main = safe_wrapper()
"#,
        "pure function cannot call",
    );
}

#[test]
fn effects_io_can_call_pure() {
    // I/O function CAN call pure functions (pure is subset of io)
    run_expect(
        r#"
@pure
fn calculate(x: i64) -> i64:
    return x * 2

@io
fn log_and_compute(x: i64) -> i64:
    return calculate(x) + 10

main = log_and_compute(20)
"#,
        50, // 20 * 2 + 10
    );
}

#[test]
fn effects_io_can_call_io() {
    // I/O function CAN call other I/O functions
    run_expect(
        r#"
extern fn print(msg)

@io
fn helper(x: i64) -> i64:
    print("helper")
    return x * 2

@io
fn caller(x: i64) -> i64:
    return helper(x) + 10

main = caller(20)
"#,
        50, // 20 * 2 + 10
    );
}

#[test]
fn effects_transitive_pure_violation() {
    // A(@pure) -> B(@pure) -> C(@io) should fail at B->C
    run_expect_compile_error(
        r#"
extern fn print(msg)

@io
fn leaf(x: i64) -> i64:
    print("leaf")
    return x

@pure
fn middle(x: i64) -> i64:
    return leaf(x) * 2

@pure
fn root(x: i64) -> i64:
    return middle(x) + 1

main = root(20)
"#,
        "pure function cannot call",
    );
}

#[test]
fn effects_unrestricted_can_call_anything() {
    // Functions without effects can call @io, @net, @fs, @unsafe, @pure
    run_expect(
        r#"
extern fn print(msg)

@io
fn io_func() -> i64:
    print("io")
    return 10

@net
fn net_func() -> i64:
    return 20

@fs
fn fs_func() -> i64:
    return 30

@pure
fn pure_func() -> i64:
    return 5

fn unrestricted() -> i64:
    return io_func() + net_func() + fs_func() + pure_func()

main = unrestricted()
"#,
        65, // 10 + 20 + 30 + 5
    );
}

