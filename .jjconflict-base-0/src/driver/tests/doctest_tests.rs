use simple_driver::doctest::{
    parse_doctest_text, parse_markdown_doctests, parse_spl_doctests, run_examples, DoctestStatus,
    Expected,
};

#[test]
fn doctest_parses_and_runs_expression() {
    let text = r#"
>>> x = 2
>>> x + 5
7
"#;

    let examples = parse_doctest_text(text, "<mem>");
    assert_eq!(examples.len(), 2);
    assert_eq!(examples[1].expected, Expected::Output("7".into()));

    let results = run_examples(&examples);
    assert!(matches!(results[0].status, DoctestStatus::Passed));
    assert!(matches!(results[1].status, DoctestStatus::Passed));
    assert_eq!(results[1].actual.trim(), "7");
}

#[test]
fn doctest_supports_multiline_blocks() {
    // Note: print outputs values without trailing newlines, so consecutive prints
    // result in concatenated output like "12" instead of "1\n2"
    let text = r#"
>>> for i in [1, 2]:
...     print i
12
"#;

    let examples = parse_doctest_text(text, "<mem>");
    assert_eq!(examples.len(), 1);

    let results = run_examples(&examples);
    assert!(
        matches!(results[0].status, DoctestStatus::Passed),
        "actual output: {}",
        results[0].actual
    );
    assert_eq!(results[0].actual.trim(), "12");
}

#[test]
fn doctest_matches_errors() {
    let text = r#"
>>> missing_var
Error: undefined variable
"#;

    let examples = parse_doctest_text(text, "<mem>");
    assert_eq!(examples.len(), 1);

    let results = run_examples(&examples);
    assert!(matches!(results[0].status, DoctestStatus::Passed));
    assert!(
        results[0].actual.starts_with("Error:"),
        "expected error output, got {}",
        results[0].actual
    );
}

#[test]
fn doctest_parses_markdown_fences() {
    let text = r#"
# Tutorial

```simple-doctest
>>> 1 + 1
2
```
"#;

    let examples = parse_markdown_doctests(text, "tutorial.md");
    assert_eq!(examples.len(), 1);
    assert_eq!(examples[0].start_line, 6);

    let results = run_examples(&examples);
    assert!(matches!(results[0].status, DoctestStatus::Passed));
}

#[test]
fn doctest_parses_markdown_sdoctest_fences() {
    let text = r#"
# Tutorial

```sdoctest
>>> 2 + 3
5
```
"#;

    let examples = parse_markdown_doctests(text, "tutorial.md");
    assert_eq!(examples.len(), 1);
    assert_eq!(examples[0].start_line, 6);

    let results = run_examples(&examples);
    assert!(matches!(results[0].status, DoctestStatus::Passed));
}

#[test]
fn doctest_parses_spl_docstrings() {
    let text = "\"\"\"
Factorial function

Examples:
```sdoctest
>>> 1 + 1
2
```
\"\"\"
fn factorial(n: Int) -> Int:
    return 1
";

    let examples = parse_spl_doctests(text, "sample.spl");
    assert_eq!(examples.len(), 1);
    assert_eq!(examples[0].expected, Expected::Output("2".into()));

    let results = run_examples(&examples);
    assert!(matches!(results[0].status, DoctestStatus::Passed));
}

#[test]
fn doctest_parses_multiple_spl_docstrings() {
    let text = "\"\"\"
First function

Examples:
```sdoctest
>>> x = 10
>>> x
10
```
\"\"\"
fn first():
    pass

\"\"\"
Second function

Examples:
```sdoctest
>>> 2 * 3
6
```
\"\"\"
fn second():
    pass
";

    let examples = parse_spl_doctests(text, "sample.spl");
    // First docstring has 2 examples (>>> x = 10, >>> x)
    // Second docstring has 1 example (>>> 2 * 3)
    // Total: 3 examples
    assert_eq!(examples.len(), 3, "Expected 3 examples but got {}", examples.len());

    let results = run_examples(&examples);
    assert!(matches!(results[0].status, DoctestStatus::Passed));
    assert!(matches!(results[1].status, DoctestStatus::Passed));
    assert!(matches!(results[2].status, DoctestStatus::Passed));
}

#[test]
fn doctest_parses_spl_with_multiple_examples_per_block() {
    let text = "\"\"\"
Math operations

Examples:
```sdoctest
>>> 1 + 1
2
>>> 2 * 3
6
>>> 10 - 5
5
```
\"\"\"
fn math_demo():
    pass
";

    let examples = parse_spl_doctests(text, "sample.spl");
    assert_eq!(examples.len(), 3);

    let results = run_examples(&examples);
    assert!(matches!(results[0].status, DoctestStatus::Passed));
    assert!(matches!(results[1].status, DoctestStatus::Passed));
    assert!(matches!(results[2].status, DoctestStatus::Passed));
}
