//! Regression tests for bounded parser recursion (stage-4 redeploy class-4 fix).
//!
//! A misparse used to drive the mutually-recursive expression/type parsers
//! without advancing, overflowing the native stack and aborting the process
//! with SIGABRT (RC=134) — silently killing stage-4 bootstrap builds. The
//! `MAX_PARSE_RECURSION_DEPTH` budget must convert that into a located,
//! graceful `parse error (recovery limit)` with a clean nonzero result and no
//! abort/overflow.
//!
//! The production driver runs parsing on the `simple-main` thread with a 64 MB
//! stack (`driver/src/main.rs` `DESIRED_STACK`). The default test-harness thread
//! stack (2 MB) is far smaller than production, so these tests run their body on
//! a thread sized like production to prove the depth budget fires *before* the
//! real stack is exhausted on the stack size the seed actually uses.

use crate::parser_impl::Parser;

const PROD_STACK: usize = 64 * 1024 * 1024; // matches driver DESIRED_STACK

fn on_prod_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .name("recovery-bound-test".to_string())
        .stack_size(PROD_STACK)
        .spawn(f)
        .expect("spawn test thread")
        .join()
        .expect("test thread must not panic/abort");
}

/// Deeply-nested expression far beyond the recursion budget must return a
/// bounded, located error — never overflow the stack / abort the process.
#[test]
fn deep_nesting_yields_bounded_error_not_overflow() {
    on_prod_stack(|| {
        // 20000 open parens: well past MAX_PARSE_RECURSION_DEPTH (512) and also
        // unbalanced, so no valid parse exists.
        let mut src = String::from("val x = ");
        src.push_str(&"(".repeat(20000));
        src.push('\n');

        let mut parser = Parser::new(&src);
        let result = parser.parse();

        assert!(
            result.is_err(),
            "deeply-nested unparseable input must error, not succeed"
        );
        let msg = format!("{}", result.unwrap_err());
        assert!(
            msg.contains("recovery limit"),
            "expected a bounded 'recovery limit' error, got: {msg}"
        );
    });
}

/// A `mut` parameter combined with deep nesting must still terminate cleanly:
/// `mut` params are accepted, and any residual deep recursion is bounded.
#[test]
fn mut_param_with_deep_nesting_terminates() {
    on_prod_stack(|| {
        let mut src = String::from("fn f(a: T, mut b: U) -> U:\n    val x = ");
        src.push_str(&"(".repeat(20000));
        src.push('\n');

        let mut parser = Parser::new(&src);
        // Must return (Ok or Err) without panicking / aborting.
        let _ = parser.parse();
    });
}

/// The `mut` parameter modifier alone must parse successfully — feature parity
/// so the self-hosted compiler sources compile under the seed.
#[test]
fn mut_param_parses_clean() {
    on_prod_stack(|| {
        let src = "fn preset_apply(preset: TargetPreset, mut options: CompileOptions) -> CompileOptions:\n    options.gc_off = preset.no_gc\n    return options\n";
        let mut parser = Parser::new(src);
        let result = parser.parse();
        assert!(result.is_ok(), "mut parameter must parse: {:?}", result.err());
    });
}
