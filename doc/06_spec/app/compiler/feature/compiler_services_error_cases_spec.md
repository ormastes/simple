# Compiler Services Error Cases Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/compiler_services_error_cases_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 30 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/compiler_services_error_cases/result.json` |

## Scenarios

- [slow] tokenize empty string returns empty list
- [slow] tokenize whitespace-only input returns empty list
- [slow] tokenize any input always returns empty list for noop
- [slow] calling tokenize twice is idempotent
- [slow] parse empty token list with empty source returns no errors
- [slow] parse non-empty token list with empty source returns no errors
- [slow] parse empty token list with non-empty source returns no errors
- [slow] calling parse twice returns empty errors both times
- [slow] desugar empty string returns empty string
- [slow] desugar whitespace-only returns whitespace unchanged
- [slow] desugar returns input text unchanged for noop
- [slow] calling desugar twice returns same result
- [slow] check empty module name returns no errors
- [slow] check nonexistent module name returns no errors for noop
- [slow] calling check multiple times returns empty each time
- [slow] lower empty module name returns no errors
- [slow] lower nonexistent module returns no errors for noop
- [slow] lower empty module name returns no errors
- [slow] lower any module returns no errors for noop
- [slow] logger has name field
- [slow] logger has level field set to 0
- [slow] load_fn returns empty string for nonexistent path
- [slow] load_fn returns empty string for empty path
- [slow] resolve_fn returns import name unchanged for noop
- [slow] resolve_fn returns empty string for empty import name
- [slow] resolve_fn with both empty args returns empty string
- [slow] supports_jit_fn always returns false for noop
- [slow] target_triple_fn always returns noop for noop backend
- [slow] two factory calls produce independent services
- [slow] noop services from different factory calls return same results
