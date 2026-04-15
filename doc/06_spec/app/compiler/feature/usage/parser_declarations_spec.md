# Parser Declaration Specification

Tests that the parser correctly parses declaration statements including

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-DECL-001 to #PARSER-DECL-025 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/parser_declarations_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that the parser correctly parses declaration statements including
structs, enums, classes, traits, modules, imports, and type aliases.

## Syntax

```simple
struct Point:
x: i64
y: i64

enum Color:
Red
Green
Blue

class Service:
field: Type

trait Printable:
fn print()

module utils:
fn helper():
pass

import module.submodule
type Alias = OriginalType
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_declarations/result.json` |

## Scenarios

- parses struct with fields
- parses struct with single field
- parses empty struct
- parses generic struct
- parses multi-param generic struct
- parses struct with struct field
- parses enum without data
- parses enum comparison
- parses enum with tuple variant
- parses enum with struct variant
- parses enum in match
- parses class with fields
- parses class with methods
- parses class with trait impl
- parses trait with method
- parses trait with default method
- parses trait extending trait
- parses inline module
- parses nested modules
- parses module with multiple items
- parses simple import
- parses specific import
- parses multiple imports
- parses simple type alias
- parses generic type alias
- parses complex type alias
- parses val declaration
- parses val with type annotation
- parses var declaration
- parses var with type annotation
- parses let declaration
- parses let with destructuring
- parses impl block for struct
- parses impl block for trait
- parses attribute on function
- parses attribute with args
- parses multiple attributes
- parses attribute on struct
