//! Nested method calls on temporary text values must use the same built-in
//! dispatch as calls on text bound to a local.
//!
//! Bug: doc/08_tracking/bug/seed_method_find_on_nested_substring_call_2026-08-25.md

use simple_compiler::interpreter;
use simple_parser::Parser;

fn run(code: &str) -> i32 {
    let mut parser = Parser::new(code);
    let module = parser.parse().expect("parse");
    interpreter::evaluate_module(&module.items).expect("evaluate")
}

#[test]
fn find_on_nested_substring_matches_bound_text() {
    let code = r#"
fn nested_position(source: text, needle: text, start: i64) -> i64:
    val relative: i64 = source.substring(start).find(needle)
    relative

fn bound_position(source: text, needle: text, start: i64) -> i64:
    val tail: text = source.substring(start)
    tail.find(needle)

fn main() -> i64:
    val nested = nested_position("hello world", "world", 2)
    val bound = bound_position("hello world", "world", 2)
    if nested == 4 and nested == bound:
        return 0
    1

main = main()
"#;

    assert_eq!(run(code), 0, "nested substring().find() must match bound text dispatch");
}

#[test]
fn nested_find_covers_missing_and_utf8_byte_offset_branches() {
    let code = r#"
fn main() -> i64:
    val missing: i64 = "hello".substring(1).find("z")
    val byte_offset: i64 = "éclair world".substring(2).find("world")
    if missing == -1 and byte_offset == 6:
        return 0
    1

main = main()
"#;

    assert_eq!(run(code), 0, "nested find must return -1 or a relative byte offset");
}

#[test]
fn nested_find_alias_does_not_consume_index_of_start_argument() {
    let code = r#"
fn main() -> i64:
    val find_alias: i64 = "ababa".substring(0).find_str("ba", 3)
    val indexed: i64 = "ababa".substring(0).index_of("ba", 3)
    if find_alias == 1 and indexed == 3:
        return 0
    1

main = main()
"#;

    assert_eq!(
        run(code),
        0,
        "find aliases stay one-argument while index_of honors its start offset",
    );
}
