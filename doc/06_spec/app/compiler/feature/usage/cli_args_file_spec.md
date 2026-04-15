# CLI Args File Extension Detection Specification

Tests file extension detection and the prefetch directive in the cli keyword. When a positional argument ends with a recognized file extension (.spl, .json, .csv, etc.), the cli system can auto-detect the type and optionally prefetch the file content before the main function runs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-007 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_file_spec.spl` |
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

Tests file extension detection and the prefetch directive in the cli keyword.
When a positional argument ends with a recognized file extension (.spl, .json,
.csv, etc.), the cli system can auto-detect the type and optionally prefetch
the file content before the main function runs.

## Syntax

```simple
cli:
    command run:
        positional file: text, ext: [".spl", ".shs"]
        prefetch: true     # read file content before dispatch

    command convert:
        positional input: text, ext: [".json", ".csv", ".sdn"]
        positional output: text
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_file/result.json` |

## Scenarios

- accepts file with matching extension
- rejects file with wrong extension
- handles file without extension
- prefetches file content when enabled
- skips prefetch when disabled
- handles missing file gracefully
