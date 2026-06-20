use simple_parser::error_recovery::ErrorHintLevel;
use simple_parser::Parser;

fn has_deprecation_warning(src: &str) -> bool {
    let mut parser = Parser::new(src);
    let _ = parser.parse();
    parser.error_hints().iter().any(|hint| {
        matches!(hint.level, ErrorHintLevel::Warning)
            && (hint.message.contains("Deprecated syntax for generic")
                || hint.message.contains("Deprecated syntax for type"))
    })
}

#[test]
fn array_indexing_does_not_emit_generic_deprecation_warning() {
    let src = "fn demo(lines: [text], i: i64) -> bool:\n    lines[i].trim() == \"\"";
    assert!(!has_deprecation_warning(src));
}

#[test]
fn array_indexing_after_less_than_backtrack_does_not_emit_generic_deprecation_warning() {
    let src = "fn demo(lines: [text], i: i64) -> i64:\n    while i < lines.len() and lines[i].trim() == \"\":\n        i = i + 1\n    i";
    assert!(!has_deprecation_warning(src));
}
