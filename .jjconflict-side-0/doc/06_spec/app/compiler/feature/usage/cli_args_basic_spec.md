# CLI Args Basic Specification

Tests for the `cli` keyword basic functionality: bool flags, string options, int options, and default values. The `cli` keyword provides declarative command-line argument parsing integrated into the language.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-001 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_basic_spec.spl` |
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

Tests for the `cli` keyword basic functionality: bool flags, string options,
int options, and default values. The `cli` keyword provides declarative
command-line argument parsing integrated into the language.

## Syntax

```simple
cli:
    verbose: false        # --verbose / -v bool flag
    output: "out.txt"     # --output / -o string option
    count: 1              # --count / -c int option
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cli_args_basic/result.json` |

## Scenarios

- parses bool flag default
- parses bool flag when set
- parses string option default
- parses string option with value
- parses string option with equals syntax
- parses int option default
- parses int option with value
- handles multiple options together
