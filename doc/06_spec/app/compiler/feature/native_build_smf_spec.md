# Native Build Smf Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/native_build_smf_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/native_build_smf/result.json` |

## Scenarios

- defaults to native-only format
- selects Both format with --emit-smf
- converts source path to cache path
- handles simple paths
- handles deeply nested paths
- produces both artifacts when emit_smf is true
