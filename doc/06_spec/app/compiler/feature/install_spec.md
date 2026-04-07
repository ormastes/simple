# Install Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/install_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/install/result.json` |

## Scenarios

- resolves latest non-yanked version
- pulls artifact from GHCR
- verifies checksum after download
- extracts to packages directory
- shows error message
- shows warning for yanked version
- selects next available version
- adds package to simple.sdn dependencies
- selects latest version when no constraint
- respects caret constraint
- respects exact version constraint
