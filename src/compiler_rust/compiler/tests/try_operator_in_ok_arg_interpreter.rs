//! `?` nested inside an `Ok(...)` argument must propagate the `Err` out of the
//! enclosing function (seed_interp_try_inside_ok_arg_no_early_return_2026-11-06).
//!
//! The record's repro `Ok(self.row(node)?.op)` is NOT a `?` followed by `.op`:
//! the lexer reads `?.` as ONE safe-navigation token (both the seed and the
//! pure-Simple lexer, `src/compiler/10.frontend/core/lexer_types.spl`), so it
//! is `Ok(self.row(node) ?. op)` and an `Err` receiver yields `nil`, giving
//! `Ok(nil)`. That is the documented `?.` grammar (syntax_quick_reference.md
//! "Safe Navigation"), not a dropped early return. The try-then-field form is
//! `(expr?).field`. These tests pin both readings so a future change to either
//! is a visible decision.
use simple_compiler::interpreter;
use std::collections::HashSet;
use std::fs;
use tempfile::tempdir;

fn run_program(main: &str) -> Result<i32, String> {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, main).unwrap();
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    let module =
        simple_compiler::pipeline::module_loader::load_module_with_imports(&main_path, &mut HashSet::new()).unwrap();
    interpreter::set_current_file(Some(main_path.to_path_buf()));
    let result = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    result.map_err(|e| format!("{e:?}"))
}

const POOL: &str = "class Row:
    op: i64
class Pool:
    rows: Dict<i64, Row>
    fn row(node: i64) -> Result<Row, text>:
        if not self.rows.contains_key(node):
            return Err(\"no row\")
        Ok(self.rows[node])
    fn op_paren(node: i64) -> Result<i64, text>:
        Ok((self.row(node)?).op)
    fn op_whole(node: i64) -> Result<Row, text>:
        Ok(self.row(node)?)
    fn op_safe_nav(node: i64) -> Result<i64, text>:
        Ok(self.row(node)?.op)
fn plain(x: i64) -> Result<i64, text>:
    if x < 0:
        return Err(\"neg\")
    Ok(x)
fn wrap(x: i64) -> Result<i64, text>:
    Ok(plain(x)? + 1)
";

fn check(body: &str) -> Result<i32, String> {
    run_program(&format!("{POOL}fn main() -> i64:\n{body}"))
}

#[test]
fn try_in_ok_arg_propagates_err_from_free_function() {
    assert_eq!(check("    if wrap(-1).is_err():\n        return 1\n    0\n"), Ok(1));
    assert_eq!(check("    if wrap(4).unwrap() == 5:\n        return 1\n    0\n"), Ok(1));
}

#[test]
fn try_in_ok_arg_propagates_err_from_method() {
    let src = "    val p = Pool(rows: {})\n    if p.op_whole(9).is_err() and p.op_paren(9).is_err():\n        return 1\n    0\n";
    assert_eq!(check(src), Ok(1));
}

#[test]
fn parenthesized_try_then_field_reads_the_ok_payload() {
    let src = "    val p = Pool(rows: {3: Row(op: 42)})\n    p.op_paren(3).unwrap()\n";
    assert_eq!(check(src), Ok(42));
}

#[test]
fn question_dot_is_safe_navigation_not_try() {
    // `?.` on an Err receiver is nil, so the method returns Ok(nil): documented
    // safe-navigation semantics, shared with the pure-Simple lexer.
    let src = "    val p = Pool(rows: {})\n    if p.op_safe_nav(9).is_ok():\n        return 1\n    0\n";
    assert_eq!(check(src), Ok(1));
}
