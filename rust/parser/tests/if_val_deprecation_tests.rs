use simple_parser::error_recovery::ErrorHintLevel;
use simple_parser::Parser;

fn parse_and_get_hints(source: &str) -> (bool, Vec<String>) {
    let mut parser = Parser::new(source);
    let ok = parser.parse().is_ok();
    let messages: Vec<String> = parser
        .error_hints()
        .iter()
        .filter(|h| h.level == ErrorHintLevel::Warning)
        .map(|h| h.message.clone())
        .collect();
    (ok, messages)
}

#[test]
fn if_let_emits_deprecation_warning() {
    let (ok, warnings) = parse_and_get_hints("if let Some(x) = opt:\n    x\n");
    assert!(ok, "if let should still parse successfully");
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("Deprecated") && w.contains("if let")),
        "expected deprecation warning for if let, got: {:?}",
        warnings
    );
}

#[test]
fn if_val_no_deprecation_warning() {
    let (ok, warnings) = parse_and_get_hints("if val Some(x) = opt:\n    x\n");
    assert!(ok, "if val should parse successfully");
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("Deprecated") && w.contains("if let")),
        "if val should NOT emit deprecation warning, got: {:?}",
        warnings
    );
}

#[test]
fn if_var_no_deprecation_warning() {
    let (ok, warnings) = parse_and_get_hints("if var Some(x) = opt:\n    x\n");
    assert!(ok, "if var should parse successfully");
    assert!(
        !warnings
            .iter()
            .any(|w| w.contains("Deprecated") && w.contains("if let")),
        "if var should NOT emit deprecation warning, got: {:?}",
        warnings
    );
}

#[test]
fn while_let_emits_deprecation_warning() {
    let (ok, warnings) = parse_and_get_hints("while let Some(x) = iter:\n    x\n");
    assert!(ok, "while let should still parse successfully");
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("Deprecated") && w.contains("if let")),
        "expected deprecation warning for while let, got: {:?}",
        warnings
    );
}
