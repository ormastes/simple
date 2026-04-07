# Windows Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/platform/windows_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/platform/windows/result.json` |

## Scenarios

- converts forward slashes to backslashes
- handles drive letters correctly
- converts UNC paths correctly
- handles mixed slashes
- detects MinGW-style paths
- rejects non-MinGW paths
- converts MinGW paths to Windows format
- converts Windows paths to MinGW format
- treats MinGW paths as absolute
- dir_sep returns backslash
- path_sep returns semicolon
- exe_ext returns .exe
- adds .exe extension to commands without extension
- preserves commands with .exe extension
- handles .bat and .cmd files
- preserves absolute paths
- joins paths with backslashes
- extracts file names from Windows paths
- handles UNC paths in Path class
- executes cmd.exe commands
- captures stdout correctly
- can check if MSVC is available
- can check if lld-link is available
- Windows linker type has string representation
