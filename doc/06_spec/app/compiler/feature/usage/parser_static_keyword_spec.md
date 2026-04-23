# Static Keyword Parsing

Tests parsing and resolution of the `static` keyword for class and struct methods. Uses ClassName.method() dot-access syntax which works in interpreter mode.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-004 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/parser_static_keyword_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests parsing and resolution of the `static` keyword for class and struct methods.
Uses ClassName.method() dot-access syntax which works in interpreter mode.

## Syntax

```simple
class Math:
    static fn add(a: i32, b: i32) -> i32:
        return a + b
val result = Math.add(2, 3)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/parser_static_keyword/result.json` |

## Scenarios

- parses static method in class
- calls static method without instance
- parses static method with no parameters
- parses static method returning text
- parses static method in impl block
- parses multiple static methods in impl
- distinguishes static from instance methods
- parses class with both static and instance methods
- uses static method as constructor alternative
- uses static method with parameters
- parses public static method
- parses private static method
- parses static generic method
- calls static method from another static method
- parses static method with default parameter
- parses static method returning array
- parses static method returning option
- parses static method with no return type
- parses static method with complex expression
- parses nested static method calls
- parses async static method
