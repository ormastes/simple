# Contextual Keyword Disambiguation

Simple treats `skip`, `static`, and `default` as contextual keywords rather than fully reserved words. This means each token can serve as either a keyword or an ordinary identifier depending on syntactic context -- specifically, whether it is followed by `(`. The spec validates all six disambiguation branches (keyword vs identifier for each of the three tokens), confirms that multiple contextual keywords can coexist as method names within a single class, and ensures that identifiers merely prefixed with a keyword name (e.g., `skip_all`) are never misinterpreted.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-012 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/parser_contextual_keywords_simple_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Simple treats `skip`, `static`, and `default` as contextual keywords rather than
fully reserved words. This means each token can serve as either a keyword or an
ordinary identifier depending on syntactic context -- specifically, whether it is
followed by `(`. The spec validates all six disambiguation branches (keyword vs
identifier for each of the three tokens), confirms that multiple contextual
keywords can coexist as method names within a single class, and ensures that
identifiers merely prefixed with a keyword name (e.g., `skip_all`) are never
misinterpreted.

## Syntax

```simple
fn skip(n):
return n * 2
val result = skip(5)

skip

class Math:
static fn add(a, b):
return a + b
Math.add(3, 7)

class Settings:
fn default():
return 200
settings.default()
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Contextual keyword | A token that acts as a keyword or identifier based on surrounding syntax |
| Lookahead disambiguation | The parser checks for a following `(` to decide identifier vs keyword |
| Branch coverage | All six branches (keyword/identifier x three tokens) are exercised |
| Coexistence | A single class can define methods named `skip`, `static`, and `default` |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/parser_contextual_keywords_simple/result.json` |

## Scenarios

- works as function name
- works as method name
- works as standalone statement
- works in function body
- works as function name
- works as method name
- works in static method declaration
- works as function name
- works as method name
- parses in match context
- allows all three keywords as method names in same class
- distinguishes keywords from underscored identifiers
