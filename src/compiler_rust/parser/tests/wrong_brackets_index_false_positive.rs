//! Regression gate: `dict[Ctor(...)]` and `buf[MAX_LEN]` are INDEX expressions,
//! not `List[T]` generics, and must not raise the "use <> for generics" hint.
//!
//! The old rule fired on `identifier[` + any capitalized identifier, which is
//! also the shape of a dict index whose key is a struct literal. Over the
//! compiler's own sources that produced 284 false warnings in a single run,
//! e.g. `recovered_constants[SymbolId(id: const_idx)] = hir_const`.
//!
//! See doc/08_tracking/bug/common_mistake_detector_false_positive_dict_index_ctor_2026-08-25.md

use simple_parser::Parser;

fn generic_bracket_hints(source: &str) -> Vec<String> {
    let mut parser = Parser::new(source);
    let _ = parser.parse();
    parser
        .error_hints()
        .iter()
        .filter(|h| h.message.contains("<> instead of []"))
        .map(|h| h.message.clone())
        .collect()
}

#[test]
fn dict_index_with_struct_literal_key_is_not_a_generic() {
    let hints = generic_bracket_hints("fn f():\n    recovered[SymbolId(id: idx)] = c\n");
    assert!(
        hints.is_empty(),
        "index with a constructor key was reported as generics: {hints:?}"
    );
}

#[test]
fn dict_index_with_screaming_snake_constant_is_not_a_generic() {
    let hints = generic_bracket_hints("fn f():\n    val x = buf[MAX_LEN]\n");
    assert!(
        hints.is_empty(),
        "index with a SCREAMING_SNAKE constant was reported as generics: {hints:?}"
    );
}

#[test]
fn index_with_qualified_key_is_not_a_generic() {
    let hints = generic_bracket_hints("fn f():\n    val x = table[Owner.id]\n");
    assert!(
        hints.is_empty(),
        "index with a qualified key was reported as generics: {hints:?}"
    );
}

#[test]
fn real_bracket_generics_are_still_reported() {
    // The detector must keep its teeth: `List[T]` is the actual mistake.
    let hints = generic_bracket_hints("fn f(xs: List[T]):\n    pass_dn\n");
    assert!(!hints.is_empty(), "the genuine List[T] mistake was no longer reported");
}
