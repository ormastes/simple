# CLI Args Error Handling Specification

Tests compile-time and runtime error cases for the cli keyword. The compiler should catch invalid cli blocks at compile time, and the runtime should produce clear error messages for bad input.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-009 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_error_spec.spl` |
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

Tests compile-time and runtime error cases for the cli keyword.
The compiler should catch invalid cli blocks at compile time,
and the runtime should produce clear error messages for bad input.

## Key Error Cases

- Duplicate option names
- Invalid default value types
- Unknown options at runtime
- Missing required positional args
- Type mismatch at runtime (e.g., "abc" for int option)
- Duplicate subcommand names
- Reserved option names (--help, --version)

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cli_args_error/result.json` |

## Scenarios

- rejects duplicate option names
- rejects invalid default expression
- rejects duplicate subcommand names
- warns on reserved option names
- reports unknown option
- reports missing value for option
- reports type mismatch
- reports missing required positional
