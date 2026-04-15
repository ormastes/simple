# Dual Argument Syntax

Tests support for both ':' and '=' as argument assignment syntax in all contexts. Covers function calls (colon, equals, and mixed syntax), struct initialization with both syntaxes including shorthand, no-paren calls via a parser-safe model, edge cases like nested calls and multiline arguments, and consistency verification ensuring both syntaxes produce identical behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/parser_dual_argument_syntax_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests support for both ':' and '=' as argument assignment syntax in all contexts.
Covers function calls (colon, equals, and mixed syntax), struct initialization with
both syntaxes including shorthand, no-paren calls via a parser-safe model, edge cases
like nested calls and multiline arguments, and consistency verification ensuring both
syntaxes produce identical behavior.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/parser_dual_argument_syntax/result.json` |

## Scenarios

- accepts single named argument with colon
- accepts multiple named arguments with colons
- accepts single named argument with equals
- accepts multiple named arguments with equals
- accepts mixed colon and equals syntax
- produces identical results regardless of syntax
- accepts single field with colon
- accepts multiple fields with colons
- accepts many fields with colons
- accepts single field with equals
- accepts multiple fields with equals
- accepts many fields with equals
- accepts mixed colon and equals syntax
- produces identical structs regardless of syntax
- accepts shorthand syntax
- mixes shorthand with explicit syntax
- accepts single argument with colon
- accepts multiple arguments with colons
- accepts single argument with equals
- accepts multiple arguments with equals
- accepts mixed colon and equals syntax
- produces identical results regardless of syntax
- handles nested function calls with mixed syntax
- handles struct init inside function call
- handles function call result in struct init 
- handles multiline with colon syntax
- handles multiline with equals syntax
- handles multiline with mixed syntax
- handles spaces around colon
- handles spaces around equals
- produces same results in all contexts combined
- works identically in real-world scenarios
