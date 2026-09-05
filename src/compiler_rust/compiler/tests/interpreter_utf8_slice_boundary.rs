//! `.slice()` / `.substring()` at a mid-codepoint byte offset must preserve the
//! RAW BYTES of the requested range.
//!
//! Bug: doc/08_tracking/bug/native_slice_splits_utf8_three_divergent_policies_2026-08-01.md
//!
//! The interpreter used to run the sliced bytes through
//! `String::from_utf8_lossy`, substituting U+FFFD. That is valid-but-wrong: it
//! CHANGES the byte length of the result (a 2-byte range came back with
//! `len() == 4`) and makes the original byte unrecoverable at concat time,
//! while bracket slicing `s[i:j]` on the SAME engine and `rt_slice` on the
//! JIT/native lanes both kept the raw bytes. The interpreter was the wrong
//! engine; slicing is byte-indexed by design, the same design that makes
//! `len()` and `index_of()` byte-valued so their results are valid inputs to
//! `slice()`.
//!
//! Every assertion below is on an integer LENGTH or a reassembled string --
//! never on a printed glyph, because `print()` renders the lossy and the raw
//! forms as the same `a<?>`.

use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(code: &str) -> i32 {
    let mut parser = Parser::new(code);
    let module = parser.parse().expect("parse");
    interpreter::evaluate_module(&module.items).expect("evaluate")
}

/// The probe string from the bug report: 11 bytes, codepoints starting at byte
/// offsets 0, 1, 3, 6, 10. Mid-codepoint offsets are 2, 4, 5, 7, 8, 9.
const PROBE: &str = r#"    val s = "a\u{E9}\u{20AC}\u{1D11E}z"
"#;

/// NOTE on spelling: the chain is written INLINE inside the `if` rather than
/// bound with `val a = s.slice(0, 2).len()`. The bound form is rejected by the
/// interpreter with `E3009: method 'len' not found on value of type str in
/// nested call context` -- a pre-existing, unrelated gap in binding a chained
/// method call to a `val`, not something this fix introduced or should paper
/// over. Filed as
/// doc/08_tracking/bug/interpreter_val_bound_chained_method_call_e3009_2026-08-21.md.
#[test]
fn slice_length_equals_the_byte_range_width_even_when_it_splits_a_codepoint() {
    // Each range below splits a multi-byte codepoint. Pre-fix these returned 4,
    // 4, 4 and 9 respectively (one U+FFFD, 3 bytes, replacing each bad byte).
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         if s.slice(0, 2).len() == 2 and s.substring(0, 2).len() == 2 \
         and s.slice(4, 6).len() == 2 and s.slice(0, 8).len() == 8:\n        \
         return 0\n    1\n\nmain = main()"
    );
    assert_eq!(run(&code), 0, "a split slice must keep the raw bytes of its range");
}

/// The same range spelled three ways must agree. This is the actual divergence
/// the bug names: bracket slicing was raw on every engine while the METHOD
/// spelling was lossy on this one, so the spelling changed the answer.
#[test]
fn bracket_slice_and_method_slice_agree_on_a_split_range() {
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         if s[0:2].len() == s.slice(0, 2).len() and s.slice(0, 2).len() == s.substring(0, 2).len():\n        \
         return 0\n    1\n\nmain = main()"
    );
    assert_eq!(
        run(&code),
        0,
        "s[0:2], s.slice(0,2) and s.substring(0,2) must have the same length"
    );
}

/// Reassembly is the invariant that U+FFFD destroyed: the original byte was
/// unrecoverable, so every fragment-stepping scanner (json/toml tokenizers)
/// silently corrupted non-ASCII input.
#[test]
fn adjacent_split_slices_reassemble_the_original() {
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         if s.slice(0, 2) + s.slice(2, 11) == s and s.slice(0, 5) + s.slice(5, 11) == s:\n        \
         return 0\n    1\n\nmain = main()"
    );
    assert_eq!(run(&code), 0, "adjacent byte slices must reassemble the original text");
}

/// Aligned ranges are the non-vacuity control: they were ALREADY correct, so a
/// change that broke them would be a regression rather than the fix.
#[test]
fn aligned_slices_are_unchanged() {
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         if s.slice(0, 1).len() == 1 and s.slice(1, 3).len() == 2 and s.slice(3, 6).len() == 3 \
         and s.slice(6, 10).len() == 4 and s.slice(0, 11) == s:\n        return 0\n    1\n\nmain = main()"
    );
    assert_eq!(run(&code), 0, "codepoint-aligned slices must be unchanged");
}

/// Empty and overrunning ranges: clamped, never panicking, and never widened by
/// a substitution.
#[test]
fn empty_and_overrun_ranges_are_clamped() {
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         if s.slice(3, 3).len() == 0 and s.slice(6, 99).len() == 5 and s.slice(99, 99).len() == 0 \
         and s.slice(2, 1).len() == 0:\n        return 0\n    1\n\nmain = main()"
    );
    assert_eq!(
        run(&code),
        0,
        "empty/overrun ranges must clamp without changing length semantics"
    );
}
