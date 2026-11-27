use simple_compiler::interpreter::{clear_bdd_state, evaluate_module, get_test_results};
use simple_parser::Parser;

fn run_examples(source: &str) -> Vec<(String, bool, bool)> {
    clear_bdd_state();
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse");
    evaluate_module(&module.items).expect("eval");
    let results = get_test_results()
        .into_iter()
        .map(|(_, name, passed, skipped)| (name, passed, skipped))
        .collect();
    clear_bdd_state();
    results
}

fn evaluate_failure(subject: &str, matcher: &str) -> String {
    clear_bdd_state();
    let source = format!("expect({subject}).{matcher}()\nmain = 0\n");
    let mut parser = Parser::new(&source);
    let module = parser.parse().expect("parse");
    let error = evaluate_module(&module.items).expect_err("strict matcher mismatch must fail");
    let message = error.to_string();
    clear_bdd_state();
    message
}

const SOURCE: &str = r#"
describe "strict boolean matchers":
    it "true passes to_be_true":
        expect(true).to_be_true()
    it "false passes to_be_false":
        expect(false).to_be_false()
    it "false fails to_be_true":
        expect(false).to_be_true()
    it "true fails to_be_false":
        expect(true).to_be_false()
    it "one fails to_be_true":
        expect(1).to_be_true()
    it "zero fails to_be_false":
        expect(0).to_be_false()
main = 0
"#;

#[test]
fn strict_matchers_accept_only_exact_boolean_values() {
    let results = run_examples(SOURCE);
    assert_eq!(results.len(), 6, "every BDD example must execute: {results:?}");
    let verdict = |name: &str| {
        results
            .iter()
            .find(|(n, _, _)| n == name)
            .map(|(_, passed, skipped)| (*passed, *skipped))
            .unwrap_or_else(|| panic!("example {name:?} did not run; results: {results:?}"))
    };

    for (name, expected) in [
        ("true passes to_be_true", true),
        ("false passes to_be_false", true),
        ("false fails to_be_true", false),
        ("true fails to_be_false", false),
        ("one fails to_be_true", false),
        ("zero fails to_be_false", false),
    ] {
        let (passed, skipped) = verdict(name);
        assert!(!skipped, "example {name:?} must execute rather than skip");
        assert_eq!(
            passed, expected,
            "unexpected strict matcher verdict for {name:?}: {results:?}"
        );
    }
}

#[test]
fn strict_matcher_failures_report_expected_and_actual_values() {
    for (subject, matcher, expected) in [
        ("false", "to_be_true", "expected true, got false"),
        ("true", "to_be_false", "expected false, got true"),
        ("1", "to_be_true", "expected true, got 1"),
        ("0", "to_be_false", "expected false, got 0"),
    ] {
        let message = evaluate_failure(subject, matcher);
        assert!(
            message.contains(expected),
            "{subject}.{matcher}() reported {message:?}, missing {expected:?}"
        );
    }
}
