# CLI Args Help Text Specification

Tests automatic help text generation from docstrings and option metadata. The cli keyword generates --help output including program description, option names with types, defaults, and short names.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-004 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_help_spec.spl` |
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

Tests automatic help text generation from docstrings and option metadata.
The cli keyword generates --help output including program description,
option names with types, defaults, and short names.

## Syntax

```simple
cli:
    verbose: false      # Enable verbose output
    output: "out.txt"   # Output file path
    count: 1            # Number of iterations
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/cli_args_help/result.json` |

## Scenarios

- responds to --help flag
- responds to -h short flag
- includes option names in help
- includes short names in help
- includes type information in help
- includes program description from docstring
