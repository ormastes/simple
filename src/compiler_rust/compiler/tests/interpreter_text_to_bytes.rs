//! `text.to_bytes()` and `text.bytes()` in the interpreter.
//!
//! The compiled lanes lower both names to `rt_string_bytes`, which returns one
//! tagged int per UTF-8 BYTE (never per char). The interpreter had `bytes` only
//! on a direct receiver, had no `to_bytes` at all ("method `to_bytes` not found
//! on type `str`"), and had neither on a chained receiver ("method 'bytes' not
//! found on value of type str in nested call context"). That failed the SCV
//! specs scv_build_snapshot_relation_v1 and structural_storage_v1 on the seed.
//!
//! Every assertion is on integer byte values, so a char-based or lossy
//! (U+FFFD) implementation cannot pass.

use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(code: &str) -> i32 {
    let mut parser = Parser::new(code);
    let module = parser.parse().expect("parse");
    interpreter::evaluate_module(&module.items).expect("evaluate")
}

/// "h\u{E9}llo" is 5 chars but 6 UTF-8 bytes: 68 C3 A9 6C 6C 6F.
const PROBE: &str = "    val s = \"h\\u{E9}llo\"\n";

#[test]
fn to_bytes_returns_utf8_bytes_on_a_direct_receiver() {
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         val a = s.to_bytes()\n    \
         if a.len() != 6: return 1\n    \
         if a[0] != 104 or a[1] != 195 or a[2] != 169 or a[5] != 111: return 2\n    \
         val b = s.bytes()\n    \
         var i = 0\n    \
         while i < 6:\n        \
         if a[i] != b[i]: return 3\n        \
         i = i + 1\n    \
         0\n\nmain = main()"
    );
    assert_eq!(run(&code), 0, "to_bytes must equal bytes: one int per UTF-8 byte");
}

#[test]
fn to_bytes_and_bytes_dispatch_on_a_chained_text_receiver() {
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         if (\" \" + s + \" \").trim().to_bytes().len() != 6: return 1\n    \
         if (\" \" + s + \" \").trim().bytes().len() != 6: return 2\n    \
         if s.to_upper().to_bytes()[0] != 72: return 3\n    \
         0\n\nmain = main()"
    );
    assert_eq!(run(&code), 0, "chained text receivers must expose UTF-8 bytes");
}

/// `s.slice(0, 2)` splits the 2-byte codepoint and yields raw, non-UTF-8 text
/// (`StrBytes`). Its bytes must come back exactly (68 C3), not through a lossy
/// U+FFFD render (68 EF BF BD).
#[test]
fn to_bytes_keeps_raw_bytes_of_a_split_codepoint() {
    let code = format!(
        "fn main() -> i64:\n{PROBE}    \
         val head = s.slice(0, 2)\n    \
         val a = head.to_bytes()\n    \
         if a.len() != 2: return 1\n    \
         if a[0] != 104 or a[1] != 195: return 2\n    \
         if head.bytes().len() != 2: return 3\n    \
         0\n\nmain = main()"
    );
    assert_eq!(run(&code), 0, "to_bytes on a split fragment must be byte-exact");
}
