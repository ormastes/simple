//! BDD FFI bridge for native/SMF test execution modes.
//!
//! Provides runtime FFI functions that mirror the interpreter's BDD state
//! management (describe/it/expect), enabling compiled tests to use the same
//! BDD framework without the interpreter.
//!
//! These functions are called by Cranelift-compiled code via the runtime FFI
//! linkage, using the same thread-local state pattern as the interpreter BDD.

use std::cell::RefCell;

use crate::value::core::RuntimeValue;

// ============================================================================
// Thread-local BDD state (mirrors interpreter_call/bdd.rs)
// ============================================================================

thread_local! {
    /// Current indentation level for nested describe blocks
    static BDD_INDENT: RefCell<usize> = RefCell::new(0);
    /// (passed, failed) counts for current describe block
    static BDD_COUNTS: RefCell<(usize, usize)> = RefCell::new((0, 0));
    /// Whether the current it-block's expect has failed
    static BDD_EXPECT_FAILED: RefCell<bool> = RefCell::new(false);
    /// Whether we are inside an it-block
    static BDD_INSIDE_IT: RefCell<bool> = RefCell::new(false);
    /// Failure message from expect
    static BDD_FAILURE_MSG: RefCell<Option<String>> = RefCell::new(None);
    /// Stack of describe block names (for nested output)
    static BDD_DESCRIBE_STACK: RefCell<Vec<String>> = RefCell::new(Vec::new());
    /// Accumulated results across all describe blocks: Vec<(total, failed)>
    static BDD_RESULTS: RefCell<Vec<(usize, usize)>> = RefCell::new(Vec::new());
    /// Before-each callback function pointers (stack per nesting level)
    static BDD_BEFORE_EACH: RefCell<Vec<Vec<i64>>> = RefCell::new(vec![vec![]]);
    /// After-each callback function pointers (stack per nesting level)
    static BDD_AFTER_EACH: RefCell<Vec<Vec<i64>>> = RefCell::new(vec![vec![]]);
}

// ============================================================================
// Helper: read a string from (ptr, len)
// ============================================================================

unsafe fn read_str(ptr: i64, len: i64) -> String {
    if ptr == 0 || len <= 0 {
        return String::new();
    }
    let slice = std::slice::from_raw_parts(ptr as *const u8, len as usize);
    String::from_utf8_lossy(slice).into_owned()
}

fn indent_str(level: usize) -> String {
    "  ".repeat(level)
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Start a describe block. Prints the description and pushes nesting level.
/// Called at the beginning of each `describe "..." { ... }` block.
#[no_mangle]
pub extern "C" fn rt_bdd_describe_start(name_ptr: i64, name_len: i64) {
    let name = unsafe { read_str(name_ptr, name_len) };

    BDD_INDENT.with(|cell| {
        let indent = *cell.borrow();
        println!("{}{}", indent_str(indent), name);
    });

    BDD_DESCRIBE_STACK.with(|cell| cell.borrow_mut().push(name));
    BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);
    BDD_COUNTS.with(|cell| *cell.borrow_mut() = (0, 0));
    BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().push(vec![]));
    BDD_AFTER_EACH.with(|cell| cell.borrow_mut().push(vec![]));
}

/// End a describe block. Prints summary "X examples, Y failures" and pops nesting.
#[no_mangle]
pub extern "C" fn rt_bdd_describe_end() {
    let (passed, failed) = BDD_COUNTS.with(|cell| *cell.borrow());
    let total = passed + failed;

    BDD_INDENT.with(|cell| {
        let indent = (*cell.borrow()).saturating_sub(1);
        *cell.borrow_mut() = indent;

        if failed == 0 {
            println!("{}\x1b[32m{} examples, 0 failures\x1b[0m", indent_str(indent), total);
        } else {
            println!(
                "{}\x1b[31m{} examples, {} failures\x1b[0m",
                indent_str(indent),
                total,
                failed
            );
        }
    });

    // Save results for this describe block
    BDD_RESULTS.with(|cell| cell.borrow_mut().push((total, failed)));

    BDD_DESCRIBE_STACK.with(|cell| cell.borrow_mut().pop());
    BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().pop());
    BDD_AFTER_EACH.with(|cell| cell.borrow_mut().pop());
}

/// Start an it-block. Resets expectation state.
/// Called at the beginning of each `it "..." { ... }` block.
#[no_mangle]
pub extern "C" fn rt_bdd_it_start(name_ptr: i64, name_len: i64) {
    let name = unsafe { read_str(name_ptr, name_len) };

    BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = false);
    BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = None);
    BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = true);

    BDD_INDENT.with(|cell| {
        let indent = *cell.borrow();
        print!("{}  {}", indent_str(indent), name);
    });
}

/// End an it-block. Updates counts and prints pass/fail indicator.
/// `passed` is 1 if the test passed (no expect failures), 0 if failed.
#[no_mangle]
pub extern "C" fn rt_bdd_it_end(passed: i64) {
    BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = false);

    let expect_failed = BDD_EXPECT_FAILED.with(|cell| *cell.borrow());
    let actually_passed = passed != 0 && !expect_failed;

    if actually_passed {
        println!(" \x1b[32m✓\x1b[0m");
    } else {
        println!(" \x1b[31m✗\x1b[0m");
        // Print failure message if available
        BDD_FAILURE_MSG.with(|cell| {
            if let Some(ref msg) = *cell.borrow() {
                BDD_INDENT.with(|indent_cell| {
                    let indent = *indent_cell.borrow();
                    println!("{}    \x1b[31m{}\x1b[0m", indent_str(indent), msg);
                });
            }
        });
    }

    BDD_COUNTS.with(|cell| {
        let (ref mut p, ref mut f) = *cell.borrow_mut();
        if actually_passed {
            *p += 1;
        } else {
            *f += 1;
        }
    });
}

/// Check if current it-block's expect has failed.
/// Returns 1 if failed, 0 if not.
#[no_mangle]
pub extern "C" fn rt_bdd_has_failure() -> i64 {
    BDD_EXPECT_FAILED.with(|cell| if *cell.borrow() { 1 } else { 0 })
}

/// Set expectation as failed with a message.
/// Called by expect matchers when assertion fails.
#[no_mangle]
pub extern "C" fn rt_bdd_expect_fail(msg_ptr: i64, msg_len: i64) {
    let msg = unsafe { read_str(msg_ptr, msg_len) };
    BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);
    BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = Some(msg));
}

/// Simple equality expectation: check if actual == expected (both as RuntimeValue i64).
/// Sets failure state if not equal.
#[no_mangle]
pub extern "C" fn rt_bdd_expect_eq(actual: i64, expected: i64) {
    if actual != expected {
        let msg = format!("Expected {} to equal {}", actual, expected);
        BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);
        BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = Some(msg));
    }
}

/// Truthy expectation: check if value is truthy (non-zero, non-nil).
/// RuntimeValue encoding: 0 = nil, bool false uses special tag.
#[no_mangle]
pub extern "C" fn rt_bdd_expect_truthy(value: i64) {
    let rv = RuntimeValue(value as u64);
    let is_truthy = !rv.is_nil() && rv.0 != 0;
    if !is_truthy {
        let msg = format!("Expected value to be truthy, got {}", value);
        BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);
        BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = Some(msg));
    }
}

/// Register a before_each callback (as function pointer).
#[no_mangle]
pub extern "C" fn rt_bdd_before_each(block: i64) {
    BDD_BEFORE_EACH.with(|cell| {
        let mut stack = cell.borrow_mut();
        if let Some(last) = stack.last_mut() {
            last.push(block);
        }
    });
}

/// Register an after_each callback (as function pointer).
#[no_mangle]
pub extern "C" fn rt_bdd_after_each(block: i64) {
    BDD_AFTER_EACH.with(|cell| {
        let mut stack = cell.borrow_mut();
        if let Some(last) = stack.last_mut() {
            last.push(block);
        }
    });
}

/// Format and print final results summary.
/// Prints total "X examples, Y failures" aggregating all describe blocks.
/// Returns the total number of failures (for exit code).
#[no_mangle]
pub extern "C" fn rt_bdd_format_results() -> i64 {
    let (total, total_failed) = BDD_RESULTS.with(|cell| {
        let results = cell.borrow();
        let mut total = 0usize;
        let mut failed = 0usize;
        for (t, f) in results.iter() {
            total += t;
            failed += f;
        }
        (total, failed)
    });

    if total_failed == 0 {
        println!("\n\x1b[32m{} examples, 0 failures\x1b[0m", total);
    } else {
        println!("\n\x1b[31m{} examples, {} failures\x1b[0m", total, total_failed);
    }

    total_failed as i64
}

/// Clear all BDD state (called between test files or at startup).
#[no_mangle]
pub extern "C" fn rt_bdd_clear_state() {
    BDD_INDENT.with(|cell| *cell.borrow_mut() = 0);
    BDD_COUNTS.with(|cell| *cell.borrow_mut() = (0, 0));
    BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = false);
    BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = false);
    BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = None);
    BDD_DESCRIBE_STACK.with(|cell| cell.borrow_mut().clear());
    BDD_RESULTS.with(|cell| cell.borrow_mut().clear());
    BDD_BEFORE_EACH.with(|cell| *cell.borrow_mut() = vec![vec![]]);
    BDD_AFTER_EACH.with(|cell| *cell.borrow_mut() = vec![vec![]]);
}

// ============================================================================
// RuntimeValue-based wrappers (for Cranelift codegen)
// ============================================================================

/// Extract a string from a RuntimeValue, returning the string content.
unsafe fn rv_to_string(rv: RuntimeValue) -> String {
    if rv.is_nil() {
        return String::new();
    }
    if rv.is_heap() {
        let ptr = rv.as_heap_ptr();
        if (*ptr).object_type == crate::value::heap::HeapObjectType::String {
            let str_ptr = ptr as *const super::collections::RuntimeString;
            return (*str_ptr).as_str().to_string();
        }
    }
    format!("{}", rv.as_int())
}

/// describe_start accepting a RuntimeValue string.
#[no_mangle]
pub extern "C" fn rt_bdd_describe_start_rv(name_rv: i64) {
    let name = unsafe { rv_to_string(RuntimeValue(name_rv as u64)) };

    BDD_INDENT.with(|cell| {
        let indent = *cell.borrow();
        println!("{}{}", indent_str(indent), name);
    });

    BDD_DESCRIBE_STACK.with(|cell| cell.borrow_mut().push(name));
    BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);
    BDD_COUNTS.with(|cell| *cell.borrow_mut() = (0, 0));
    BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().push(vec![]));
    BDD_AFTER_EACH.with(|cell| cell.borrow_mut().push(vec![]));
}

/// it_start accepting a RuntimeValue string.
#[no_mangle]
pub extern "C" fn rt_bdd_it_start_rv(name_rv: i64) {
    let name = unsafe { rv_to_string(RuntimeValue(name_rv as u64)) };

    BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = false);
    BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = None);
    BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = true);

    BDD_INDENT.with(|cell| {
        let indent = *cell.borrow();
        print!("{}  {}", indent_str(indent), name);
    });
}

/// expect_eq accepting RuntimeValues directly.
#[no_mangle]
pub extern "C" fn rt_bdd_expect_eq_rv(actual: i64, expected: i64) {
    let actual_rv = RuntimeValue(actual as u64);
    let expected_rv = RuntimeValue(expected as u64);
    // Compare as RuntimeValues
    if actual_rv != expected_rv {
        let msg = format!("Expected {} to equal {}", actual, expected);
        BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);
        BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = Some(msg));
    }
}

/// expect_truthy accepting a RuntimeValue.
#[no_mangle]
pub extern "C" fn rt_bdd_expect_truthy_rv(value: i64) {
    let rv = RuntimeValue(value as u64);
    let is_truthy = !rv.is_nil() && rv.as_bool();
    if !is_truthy {
        let msg = format!("Expected value to be truthy, got {:?}", rv);
        BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);
        BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = Some(msg));
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bdd_describe_start_end() {
        rt_bdd_clear_state();
        let name = "TestSuite";
        rt_bdd_describe_start(name.as_ptr() as i64, name.len() as i64);
        rt_bdd_describe_end();
        // Should have recorded one result block with 0 total
        BDD_RESULTS.with(|cell| {
            assert_eq!(cell.borrow().len(), 1);
            assert_eq!(cell.borrow()[0], (0, 0));
        });
    }

    #[test]
    fn test_bdd_it_pass() {
        rt_bdd_clear_state();
        let desc = "Test";
        rt_bdd_describe_start(desc.as_ptr() as i64, desc.len() as i64);

        let it_name = "should work";
        rt_bdd_it_start(it_name.as_ptr() as i64, it_name.len() as i64);
        rt_bdd_it_end(1); // passed

        rt_bdd_describe_end();

        BDD_RESULTS.with(|cell| {
            assert_eq!(cell.borrow()[0], (1, 0)); // 1 total, 0 failed
        });
    }

    #[test]
    fn test_bdd_it_fail() {
        rt_bdd_clear_state();
        let desc = "Test";
        rt_bdd_describe_start(desc.as_ptr() as i64, desc.len() as i64);

        let it_name = "should fail";
        rt_bdd_it_start(it_name.as_ptr() as i64, it_name.len() as i64);
        rt_bdd_expect_eq(1, 2); // will fail
        rt_bdd_it_end(1); // passed=1 but expect failed

        rt_bdd_describe_end();

        BDD_RESULTS.with(|cell| {
            assert_eq!(cell.borrow()[0], (1, 1)); // 1 total, 1 failed
        });
    }

    #[test]
    fn test_bdd_expect_truthy() {
        rt_bdd_clear_state();
        // RuntimeValue for integer 42
        let val = RuntimeValue::from_int(42);
        rt_bdd_expect_truthy(val.0 as i64);
        assert_eq!(rt_bdd_has_failure(), 0);
    }

    #[test]
    fn test_bdd_format_results() {
        rt_bdd_clear_state();
        BDD_RESULTS.with(|cell| {
            cell.borrow_mut().push((5, 1));
            cell.borrow_mut().push((3, 0));
        });
        let failures = rt_bdd_format_results();
        assert_eq!(failures, 1);
    }
}
