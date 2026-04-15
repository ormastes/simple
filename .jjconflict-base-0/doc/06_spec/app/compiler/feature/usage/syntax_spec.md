# Simple Language Syntax Specification - Test Specification

Comprehensive tests for Simple's syntax, including literals, string interpolation, operators, and indentation-based parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #10-19 |
| Status | Stable |
| Source | `test/feature/usage/syntax_spec.spl` |
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

**Keywords:** syntax, lexical, operators, indentation
**Last Updated:** 2026-02-08
**Topics:** syntax, type-system
**Symbols:** Token, Operator, Parser, Lexer
**Module:** simple_parser
**Migrated From:** doc/06_spec/syntax.md

## Overview

Comprehensive tests for Simple's syntax, including literals, string interpolation,
operators, and indentation-based parsing.

Simple uses Python-like indentation with type annotations and explicit execution mode control.

## Related Specifications

- **Types** - Type annotations and type syntax
- **Functions** - Function definition syntax
- **Parser** - Parser implementation details

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/syntax/result.json` |

## Scenarios

- syntax overview - if/else
- syntax overview - iteration
- literals - integer formats
- literals - floating point
- literals - typed suffixes
- string literals - interpolation
- string literals - raw strings
- string literals - basic interpolation
- functional update syntax - arrays
- functional update syntax - basic
- functional update syntax - lists
- functional update syntax - pattern 1
- functional update syntax - pattern 2
- parsing design rationale - simplicity
- parsing design rationale - lambdas
