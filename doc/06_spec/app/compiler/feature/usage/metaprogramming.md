# Simple Language Metaprogramming - Test Specification

This file contains executable test cases for metaprogramming features that are currently implemented in Simple's runtime.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Various |
| Status | Partial Implementation |
| Type | Extracted Examples |
| Reference | metaprogramming.md |
| Source | `test/feature/usage/metaprogramming_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

**Last Updated:** 2026-02-08

## Overview

This file contains executable test cases for metaprogramming features that are
currently implemented in Simple's runtime.

Tests cover: comprehensions, indexing, pattern matching, and basic error handling.

**Note:** Advanced features (DSL blocks, decorators, slicing, context managers, move closures)
are not yet fully implemented.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/metaprogramming/result.json` |

## Scenarios

- list comprehensions
- list comprehensions - transformation
- array indexing - basic
- array indexing - last element
- pattern matching - guard patterns
- pattern matching - simple matching
- error handling - safe division
- error handling - option pattern
