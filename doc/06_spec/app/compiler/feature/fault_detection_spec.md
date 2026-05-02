# Fault Detection Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/fault_detection_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
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
| `result.json` | JSON artifact | `build/test-artifacts/feature/app/fault_detection/result.json` |

## Scenarios

- enables detection and allows shallow recursion
- allows zero-depth call
- allows single recursion step
- works when disabled
- accepts small depth limit
- accepts large depth limit
- disables timeout with zero
- sets large timeout without affecting fast code
- sets execution limit
- disables execution limit with zero
- enables detection
- disables detection
- sets a custom limit
- sets and clears timeout
- sets a custom limit
- restores default configuration
- creates default config
- creates strict config
- creates permissive config
- creates disabled config
- applies default config
- applies strict config
- applies permissive config
- applies disabled config and re-enables
- creates config with custom timeout
- creates config with custom depth
- creates config with custom execution limit
- chains multiple builders
- has correct default max recursion depth
- has correct default execution limit
- has correct default timeout
- handles fibonacci computation
- handles multiple sequential recursive calls
- handles iterative loops
- toggle on-off-on preserves correctness
- all features active with fast code
