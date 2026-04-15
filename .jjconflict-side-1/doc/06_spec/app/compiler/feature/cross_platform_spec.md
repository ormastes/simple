# Cross Platform Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/platform/cross_platform_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/platform/cross_platform/result.json` |

## Scenarios

- detects current operating system
- is_unix returns true on Unix-like systems
- is_windows and is_unix are mutually exclusive
- dir_sep returns platform-specific directory separator
- path_sep returns platform-specific PATH separator
- exe_ext returns correct executable extension
- lib_ext returns correct library extension
- join_path combines path components
- normalize_path handles forward slashes
- is_absolute_path detects absolute paths
- shell executes simple commands
- detects system linker and provides info
