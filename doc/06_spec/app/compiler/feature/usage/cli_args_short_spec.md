# CLI Args Short Names Specification

Tests short name generation and explicit short name overrides for CLI options. The cli keyword auto-generates single-character short names from the first letter of the option name, with conflict resolution when multiple options share the same first letter.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-003 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_short_spec.spl` |
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

Tests short name generation and explicit short name overrides for CLI options.
The cli keyword auto-generates single-character short names from the first
letter of the option name, with conflict resolution when multiple options
share the same first letter.

## Syntax

```simple
cli:
    verbose: false                # auto-short: -v
    output: "out.txt"             # auto-short: -o
    count: 1, short: "c"         # explicit short: -c
    color: true, short: "C"      # explicit short: -C (avoids conflict with count)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_short/result.json` |

## Scenarios

- generates short from first letter
- generates short for string option
- generates short for int option
- uses explicit short name
- allows uppercase short name
- skips short when conflict exists
- resolves conflict with explicit short
- handles no available short name
