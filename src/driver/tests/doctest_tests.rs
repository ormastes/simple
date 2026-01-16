use simple_driver::doctest::{
    discover_md_doctests, parse_doctest_text, parse_markdown_doctests, parse_readme_config, parse_spl_doctests,
    run_examples, DoctestStatus, Expected,
};
use std::path::Path;

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
    // Note: print outputs values with trailing newlines, so consecutive prints
    // result in separate lines like "1\n2"
    let text = r#"
>>> for i in [1, 2]:
...     print(i)
1
2
"#;

    let examples = parse_doctest_text(text, "<mem>");
    assert_eq!(examples.len(), 1);

    let results = run_examples(&examples);
    assert!(
        matches!(results[0].status, DoctestStatus::Passed),
        "actual output: {}",
        results[0].actual
    );
    assert_eq!(results[0].actual.trim(), "1\n2");
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

// ============================================================================
// README.md-based Doctest Tests
// ============================================================================

#[test]
fn doctest_parses_readme_config_excludes() {
    let content = r#"<!--doctest:exclude
drafts/
archive/**
-->

# Title

Some content here.
"#;

    let parsed = parse_readme_config(content);
    assert_eq!(parsed.config.excludes.len(), 2);
    assert!(parsed.config.excludes.contains(&"drafts/".to_string()));
    assert!(parsed.config.excludes.contains(&"archive/**".to_string()));
}

#[test]
fn doctest_parses_readme_config_lang_and_timeout() {
    let content = r#"<!--doctest:config
lang: simple
timeout: 10000
-->

# Title
"#;

    let parsed = parse_readme_config(content);
    assert_eq!(parsed.config.lang, "simple");
    assert_eq!(parsed.config.timeout, 10000);
}

#[test]
fn doctest_parses_readme_subdirs_and_files() {
    let content = r#"# Documentation

## Subdirectory

- [API](api/)
- [Guides](guides/)

## Files

- [Usage](usage.md)
- [Reference](reference.md)
"#;

    let parsed = parse_readme_config(content);
    assert_eq!(parsed.subdirs.len(), 2);
    assert_eq!(parsed.files.len(), 2);
    assert_eq!(parsed.subdirs[0].path, "api");
    assert_eq!(parsed.subdirs[1].path, "guides");
    assert_eq!(parsed.files[0].path, "usage.md");
    assert_eq!(parsed.files[1].path, "reference.md");
}

#[test]
fn doctest_discovers_md_doctests_from_fixtures() {
    let fixtures_path = Path::new("simple/std_lib/test/fixtures/doctest/md_readme");

    if !fixtures_path.exists() {
        // Skip if fixtures don't exist
        return;
    }

    let examples = discover_md_doctests(fixtures_path).expect("Should discover md doctests");

    // Should find 5 examples: 2 from README.md, 1 from api/README.md, 2 from usage.md
    assert_eq!(examples.len(), 5, "Expected 5 doctests but found {}", examples.len());
}

#[test]
fn doctest_runs_md_doctests_from_fixtures() {
    let fixtures_path = Path::new("simple/std_lib/test/fixtures/doctest/md_readme");

    if !fixtures_path.exists() {
        // Skip if fixtures don't exist
        return;
    }

    let examples = discover_md_doctests(fixtures_path).expect("Should discover md doctests");
    let results = run_examples(&examples);

    // All 5 examples should pass
    for (i, result) in results.iter().enumerate() {
        assert!(
            matches!(result.status, DoctestStatus::Passed),
            "Example {} failed: {:?}",
            i,
            result.status
        );
    }
}

#[test]
fn doctest_readme_config_disabled() {
    let content = r#"<!--doctest:config
disabled: true
-->

# Disabled Section

```simple
# doctest
let x = 1
# expected: 1
x
```
"#;

    let parsed = parse_readme_config(content);
    assert!(parsed.config.disabled);
}
