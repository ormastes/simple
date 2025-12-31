
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
