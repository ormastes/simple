# Mir Native Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/compiler/mir_native_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/compiler/mir_native/result.json` |

## Scenarios

- runs ISel on manually constructed MIR module
- produces non-empty ELF from MIR module
- runs hello MIR binary and produces correct output
