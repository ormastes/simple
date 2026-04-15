# Skip Keyword - Comprehensive

Comprehensive tests for the `skip` keyword covering lexer token recognition, statement parsing, control flow interactions (if, loop, break, continue, return), function/method/lambda contexts, class/struct/impl blocks, async contexts, match/pattern contexts, expression flow, error handling, edge cases (nesting, comments, whitespace), and runtime semantics.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-003 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/parser_skip_keyword_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Comprehensive tests for the `skip` keyword covering lexer token recognition,
statement parsing, control flow interactions (if, loop, break, continue, return),
function/method/lambda contexts, class/struct/impl blocks, async contexts,
match/pattern contexts, expression flow, error handling, edge cases
(nesting, comments, whitespace), and runtime semantics.

## Syntax

```simple
skip
skip:
val x = 1
fn with_skip(): skip; return 42
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_skip_keyword/result.json` |

## Scenarios

- recognizes skip as a keyword token
- allows skip_func as function name
- distinguishes skip keyword from skip variable name
- allows skip in string literals
- parses skip as standalone statement
- parses skip with indented block
- parses multiple skip statements
- parses skip inside if block
- parses skip inside loop
- parses skip with break in same function
- parses skip with continue in same function
- parses skip with return in same function
- parses skip in function body
- parses skip in method body
- parses skip in static method
- parses skip in lambda
- parses skip in class method
- parses skip in impl block method
- parses skip in async function
- parses skip before await
- parses skip in match arm
- parses skip in multiple match arms
- parses skip before expression
- parses skip between declarations
- parses skip in complex expression flow
- parses skip in try-catch block
- parses skip before result return
- parses skip at start of file
- parses skip at end of function
- parses skip with empty block
- parses nested skip statements
- parses skip with comment
- parses skip with multiline comment
- parses skip with various indentation
- parses skip with no trailing whitespace
- parses skip with blank lines after
- skip statement does not prevent execution
- skip does not affect variable scope
- skip does not affect return value
- skip does not affect loop iteration
- allows skip for test tagging preparation
- parses skip with test metadata
