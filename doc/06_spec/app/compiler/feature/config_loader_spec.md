# Config Loader Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/app/config_loader_spec.spl` |
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

Documentation was generated from executable SSpec scenarios.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/app/config_loader/result.json` |

## Scenarios

- stores basic integers
- stores floats
- stores booleans
- stores strings
- stores identifiers as string constants
- stores arrays
- stores nested values
- skips comments are pure-text concern
- handles multiline config
- gets simple values
- gets nested values
- handles missing keys with default
- merges configs with overlay precedence
