# Indentation-Based Blocks Specification

Indentation-based blocks use Python-style significant whitespace to delimit code blocks instead of braces. This feature provides clean, readable syntax for function bodies, control flow, and other block-structured code in Simple.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #840-845 |
| Category | Syntax |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/indentation_blocks_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Indentation-based blocks use Python-style significant whitespace to delimit code blocks
instead of braces. This feature provides clean, readable syntax for function bodies,
control flow, and other block-structured code in Simple.

## Syntax

```simple
fn add(a: i64, b: i64) -> i64:
a + b

if condition:
do_something()
else:
do_alternative()

loop:
if inner_condition:
process()
continue
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Indentation | Whitespace level determines block scope |
| Dedentation | Return to previous indentation level |
| Colon | Marks beginning of indented block |
| Continuation | Lines can continue to next with indentation |

## Behavior

- Indentation level determines block membership
- Consistent indentation required within a block
- Tab and space mixing is not allowed
- Indentation can use either tabs or spaces (configured at parse)
- Dedentation marks end of block and returns to outer scope

## Related Specifications

- [Lexer](../lexer/lexer_spec.spl) - Token recognition including indentation
- [Parser](../parser/parser_spec.spl) - Block structure parsing
- [Syntax](../syntax/syntax_spec.spl) - Language syntax overview

## Implementation Notes

Indentation handling in lexer:
- Track indentation stack as separate token stream
- INDENT token marks increase in indentation
- DEDENT token marks decrease in indentation
- Implicit DEDENT at end of file if needed
- Error on inconsistent indentation mixing

## Examples

```simple
fn process_data(items: List<Int>) -> i64:
var total = 0
for item in items:
if item > 0:
total = total + item
else:
total = total - item
total
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/indentation_blocks/result.json` |

## Scenarios

- recognizes indented function body
- handles nested function definitions
- handles if-else indentation
- handles loop indentation
- handles nested control flow
- executes multiple statements
- mixes different statement types
- maintains block indentation
- terminates block on dedent
- handles deep nesting
- mixes nested block types
- handles if expression indentation
- uses indented blocks as values
- handles empty block
- handles single-statement block
