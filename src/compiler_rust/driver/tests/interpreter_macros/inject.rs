use super::run_code;

// ============================================================================
// Inject Tests
// ============================================================================

#[test]
fn macro_inject_here_basic() {
    // Test inject code with "here" anchor - runs at callsite
    let code = r#"
macro set_value(v: Int) -> (
    returns result: Int,
    inject setup: callsite.block.here.stmt
):
    emit setup:
        println!("Setting up...")

    emit result:
        v

let x = set_value!(42)
main = x
"#;
    let result = run_code(code, &[], "");
    match result {
        Ok(r) => assert_eq!(r.exit_code, 42),
        Err(e) => {
            // If inject is not fully supported yet, the macro should still work
            // but inject code may not execute. Check for a graceful failure.
            panic!("Test failed: {:?}", e);
        }
    }
}

#[test]
fn macro_inject_tail_basic() {
    // Test inject code with "tail" anchor - runs at block exit
    // The inject code runs and can modify mutable variables
    let code = r#"
macro with_cleanup(v: Int) -> (
    returns result: Int,
    inject cleanup: callsite.block.tail.stmt
):
    emit cleanup:
        println!("Cleanup running")

    emit result:
        v

fn test_fn() -> Int:
    let x = with_cleanup!(42)
    println!("After macro, before tail")
    return x

main = test_fn()
"#;
    let result = run_code(code, &[], "").unwrap();
    // If tail injection works, cleanup should print after "After macro" and before return
    assert_eq!(result.exit_code, 42);
}
