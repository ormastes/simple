//! Evidence test for PR #7952: unknown-method errors carry the module file.
//!
//! `bail_unknown_method!` (`src/compiler/src/interpreter/error_macros.rs`)
//! attaches `while evaluating module: <file>` (and sets the error's file) on
//! the error path whenever the interpreter has a current file. This pins that
//! diagnostic so the location probe for
//! doc/08_tracking/bug/phase2_stage2_native_build_len_on_i64_aarch64_linux_2026-09-13.md
//! cannot silently regress on the dispatch paths that use the macro.
//!
//! `set_current_file` / `get_current_file` are process-wide, so all
//! file-sensitive assertions live in this single test function (order-safe).

use simple_compiler::error::CompileError;
use simple_compiler::interpreter;
use simple_parser::Parser;
use std::path::PathBuf;

const DIAG_FILE: &str = "/tmp/unknown_method_module_note_probe.spl";

fn evaluate(source: &str) -> Result<i32, CompileError> {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    interpreter::set_current_file(Some(PathBuf::from(DIAG_FILE)));
    let module = Parser::new(source).parse().unwrap();
    interpreter::evaluate_module(&module.items)
}

fn semantic_context(err: &CompileError) -> &simple_compiler::error::ErrorContext {
    match err {
        CompileError::SemanticWithContext(ce) => &ce.context,
        other => panic!("expected SemanticWithContext, got: {other:?}"),
    }
}

const CLASS_UNKNOWN_METHOD_SRC: &str =
    "class Box:\n    v: i64\n\nfn main() -> i64:\n    let b = Box { v: 5 }\n    return b.lenn()\n";

#[test]
fn unknown_method_error_names_evaluating_module() {
    // Class-object dispatch goes through `bail_unknown_method!`: the error
    // must carry the current module file and the "while evaluating module"
    // note added by PR #7952.
    let err = evaluate(CLASS_UNKNOWN_METHOD_SRC).expect_err("b.lenn() must fail");
    let msg = err.to_string();
    assert!(
        msg.contains("method `lenn` not found on type `Box`"),
        "expected unknown-method error for lenn on Box, got: {msg}"
    );
    let ctx = semantic_context(&err);
    assert_eq!(
        ctx.file.as_deref(),
        Some(DIAG_FILE),
        "error must carry the current module file"
    );
    assert!(
        ctx.notes
            .iter()
            .any(|n| n == &format!("while evaluating module: {DIAG_FILE}")),
        "error notes must name the evaluating module, got notes: {:?}",
        ctx.notes
    );
}

const I64_LEN_SRC: &str = "fn main() -> i64:\n    let x: i64 = 5\n    return x.len()\n";

#[test]
fn unknown_method_on_i64_primitive_still_reports_type() {
    // Receiver-shape from the tracking bug (len on i64). NOTE: the primitive
    // dispatch tail in `interpreter_method/mod.rs` (~evaluate_method_call
    // "Last resort" arm) builds its ErrorContext manually and does NOT go
    // through `bail_unknown_method!`, so this path currently does NOT carry
    // the module note — verified empirically 2026-11-09. This test pins only
    // the error identity; extending the location probe to that manual site is
    // follow-up work on the tracking bug.
    let err = evaluate(I64_LEN_SRC).expect_err("x.len() on i64 must fail");
    let msg = err.to_string();
    assert!(
        msg.contains("method `len` not found on type `i64`"),
        "expected unknown-method error for len on i64, got: {msg}"
    );
}
