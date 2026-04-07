# Type Inference String Slice Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/compiler/type_inference_string_slice_spec.spl` |
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

## Overview

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/compiler/type_inference_string_slice/result.json` |

## Scenarios

- infers sliced string as text
- allows method calls on sliced strings
- infers mid-range slice as text
- infers correctly in if branches
- infers correctly with variable assignment
- doesn't confuse string slice with enum
- handles multiple string operations after slice
- works with explicit type annotation
