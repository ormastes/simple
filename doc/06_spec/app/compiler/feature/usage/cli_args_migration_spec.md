# CLI Args Migration Compatibility Specification

Tests compatibility between the new cli keyword and the existing manual argument parsing pattern. Projects using manual arg parsing should be able to incrementally migrate to the cli keyword without breaking existing functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-011 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_migration_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests compatibility between the new cli keyword and the existing manual
argument parsing pattern. Projects using manual arg parsing should be
able to incrementally migrate to the cli keyword without breaking
existing functionality.

## Manual Pattern (Before)

```simple
val args = get_args()
var verbose = false
var output = "default.txt"
for arg in args:
    if arg == "--verbose":
        verbose = true
    elif arg == "--output":
        output = next_arg()
```

## CLI Keyword (After)

```simple
cli:
    verbose: false
    output: "default.txt"
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_migration/result.json` |

## Scenarios

- produces same defaults as manual parsing
- produces same parsed values as manual parsing
- can coexist with manual parsing in same project
- supports gradual option-by-option migration
