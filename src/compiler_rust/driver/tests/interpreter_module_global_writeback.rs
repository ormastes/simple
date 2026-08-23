//! Module-level globals must observe every write-back path.
//!
//! Identifier evaluation prefers `MODULE_GLOBALS` over `env` for non-local
//! names (`compiler/src/interpreter/expr/literals.rs`), so any path that
//! updates a caller binding by writing `env` alone leaves the stale value
//! visible — silently, with a wrong number or an empty container rather than
//! an error. Two such paths were fixed together; these are their reproduce
//! cases plus same-class neighbours.

use simple_driver::interpreter::run_code;

fn exit_code(code: &str) -> i32 {
    run_code(code, &[], "").unwrap().exit_code
}

// --- while/for loop fast paths (interpreter_control.rs) ---------------------

#[test]
fn module_global_while_loop_accumulator_is_visible() {
    // The `target = target <op> index` fast path wrote only `env`.
    assert_eq!(
        exit_code("var sum = 0\nvar i = 0\nwhile i < 5:\n    sum = sum + i\n    i = i + 1\nmain = sum\n"),
        10
    );
}

#[test]
fn module_global_while_loop_index_is_visible() {
    assert_eq!(
        exit_code("var sum = 0\nvar i = 0\nwhile i < 5:\n    sum = sum + i\n    i = i + 1\nmain = i\n"),
        5
    );
}

#[test]
fn module_global_while_loop_multiply_accumulator_is_visible() {
    assert_eq!(
        exit_code("var acc = 1\nvar i = 1\nwhile i < 5:\n    acc = acc * i\n    i = i + 1\nmain = acc\n"),
        24
    );
}

#[test]
fn module_global_while_loop_result_readable_from_function() {
    assert_eq!(
        exit_code(
            "var sum = 0\nvar i = 0\nwhile i < 5:\n    sum = sum + i\n    i = i + 1\n\nfn read() -> i64:\n    return sum\n\nmain = read()\n"
        ),
        10
    );
}

// --- mutable-argument write-back (function_exec.rs / method execution.rs) ---

#[test]
fn module_global_array_mutated_by_function_argument() {
    assert_eq!(
        exit_code("fn append_answer(dest):\n    dest.push(42)\n    return 0\n\nlet out = []\nappend_answer(out)\nmain = out[0]\n"),
        42
    );
}

#[test]
fn module_global_array_mutated_by_method_argument() {
    assert_eq!(
        exit_code(
            "class Copier:\n    fn append_answer(self, dest):\n        dest.push(42)\n        return 0\n\nlet out = []\nlet copier = Copier {}\ncopier.append_answer(out)\nmain = out[0]\n"
        ),
        42
    );
}

#[test]
fn module_global_non_empty_array_mutated_by_method_argument() {
    assert_eq!(
        exit_code(
            "class Copier:\n    fn append_answer(self, dest):\n        dest.push(42)\n        return 0\n\nlet out = [7]\nlet copier = Copier {}\ncopier.append_answer(out)\nmain = out[1]\n"
        ),
        42
    );
}

#[test]
fn module_global_dict_mutated_by_function_argument() {
    assert_eq!(
        exit_code("fn fill(d):\n    d[\"k\"] = 42\n    return 0\n\nlet out = {}\nfill(out)\nmain = out[\"k\"]\n"),
        42
    );
}
