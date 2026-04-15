# CLI Args Subcommand Specification

Tests subcommand dispatch with the `cli` keyword. Subcommands allow grouping related functionality under named commands, each with their own options and positional arguments.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-005 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_subcommand_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Tests subcommand dispatch with the `cli` keyword. Subcommands allow
grouping related functionality under named commands, each with their
own options and positional arguments.

## Syntax

```simple
cli:
    verbose: false

    command build:
        target: "debug"       # --target option for build
        release: false        # --release flag for build

    command test:
        filter: ""            # --filter option for test
        parallel: true        # --parallel flag for test

    command run:
        positional file: text  # positional argument
        args: []               # pass-through remaining args
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_subcommand/result.json` |

## Scenarios

- dispatches to named subcommand
- parses subcommand-specific options
- isolates options per subcommand
- inherits global options in subcommands
- parses positional argument
- requires positional argument
- handles multiple positional args
- collects remaining args after --
- passes empty rest when no -- separator
- uses default when no subcommand specified
