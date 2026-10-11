// Regression: the generic BDD negation path (`expect(x).not.<matcher>`,
// `evaluate_negated_bdd_matcher` in interpreter_method/mod.rs) runs the
// matcher in its positive form and suppresses that form's failure state.
//
// It used to restore only the HARD flag (BDD_EXPECT_FAILED/BDD_FAILURE_MSG).
// Re-evaluating `expect(<falsy subject>)` also raises the PROVISIONAL
// hollow-expect flag (BDD_EXPECT_PROVISIONAL/BDD_PROVISIONAL_MSG), which only
// the built-in matcher arms clear. A `to_*` matcher outside that list left the
// provisional standing, so a negation that PASSED still failed the example at
// its end with "expected subject to be truthy, got false".

use simple_compiler::interpreter::{clear_bdd_state, evaluate_module, get_test_results};
use simple_parser::Parser;

fn run_examples(source: &str) -> Vec<(String, bool)> {
    clear_bdd_state();
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse");
    evaluate_module(&module.items).expect("eval");
    let results = get_test_results()
        .into_iter()
        .map(|(_, name, passed, _)| (name, passed))
        .collect();
    clear_bdd_state();
    results
}

const SOURCE: &str = r#"
trait Holds:
    fn to_hold() -> bool

impl Holds for bool:
    fn to_hold() -> bool:
        self

describe "negated provisional-raising matcher":
    it "falsy subject that does not match":
        expect(false).not.to_hold()
    it "truthy subject that matches":
        expect(true).not.to_hold()
    it "bare falsy expect still fails":
        expect(false)
main = 0
"#;

#[test]
fn negated_matcher_does_not_leak_the_positive_forms_provisional_failure() {
    let results = run_examples(SOURCE);
    let verdict = |name: &str| {
        results
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, passed)| *passed)
            .unwrap_or_else(|| panic!("example {name:?} did not run; results: {results:?}"))
    };
    assert!(
        verdict("falsy subject that does not match"),
        "`expect(false).not.to_hold()` must pass: the positive form's provisional must not leak; results: {results:?}"
    );
    assert!(
        !verdict("truthy subject that matches"),
        "`expect(true).not.to_hold()` must fail: the positive form matched; results: {results:?}"
    );
    assert!(
        !verdict("bare falsy expect still fails"),
        "a matcher-less `expect(false)` must still fail (provisional restore is scoped); results: {results:?}"
    );
}
