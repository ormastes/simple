# Numbered Placeholder Lambda Expressions

Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit parameter ordering in lambda shorthand. Covers basic single-parameter usage with map and filter, method calls on numbered placeholders, compound arithmetic expressions, edge cases (empty collections, single elements), and chaining filter/map operations with numbered placeholders.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/feature/usage/numbered_placeholder_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests numbered placeholder lambda expressions (`_1`, `_2`) which allow explicit
parameter ordering in lambda shorthand. Covers basic single-parameter usage with map
and filter, method calls on numbered placeholders, compound arithmetic expressions,
edge cases (empty collections, single elements), and chaining filter/map operations
with numbered placeholders.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/numbered_placeholder/result.json` |

## Scenarios

- uses _1 as single param
- uses _1 in filter
- uses _1 with addition
- uses _1 and _2 in order
- calls method on _1
- uses _1 in modulo
- uses _1 in compound arithmetic
- numbered on empty collection
- numbered on single element
- works with any
- works with all
- chains filter then map with numbered
- chains map then filter with numbered
