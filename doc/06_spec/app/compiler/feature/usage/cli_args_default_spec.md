# CLI Args Default Command Specification

Tests default command behavior when no subcommand is specified. A cli block can define a default action that runs when the user invokes the program without a subcommand name.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-006 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_default_spec.spl` |
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

Tests default command behavior when no subcommand is specified.
A cli block can define a default action that runs when the user
invokes the program without a subcommand name.

## Syntax

```simple
cli:
    verbose: false

    default:
        positional file: text

    command build:
        target: "debug"
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_default/result.json` |

## Scenarios

- uses default block when no subcommand given
- prefers subcommand over default when given
- shows help when no subcommand and no default
- accepts global options without subcommand
