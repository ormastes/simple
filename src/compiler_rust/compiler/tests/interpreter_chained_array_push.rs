//! Array push keeps its value semantics when invoked through a chained receiver.
use simple_compiler::interpreter;
use simple_parser::Parser;
fn run(source: &str) -> i32 {
    interpreter::evaluate_module(&Parser::new(source).parse().unwrap().items).unwrap()
}
#[test]
fn double_chain_push_returns_new_array_and_preserves_original() {
    assert_eq!(run("fn source(values: [i64]) -> [i64]:\n    values\nval original = [1]\nval updated = source(original).push(2).push(3)\nmain = original.len() * 10 + updated.len()\n"), 13);
}
#[test]
fn double_chain_append_returns_new_array_and_preserves_original() {
    assert_eq!(run("fn source(values: [i64]) -> [i64]:\n    values\nval original = [1]\nval updated = source(original).append(2).append(3)\nmain = original.len() * 10 + updated.len()\n"), 13);
}
