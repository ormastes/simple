# CLI Args mod.spl Embedding Specification

Tests embedding the cli keyword in mod.spl module files. When a module's mod.spl contains a cli block, the module becomes an executable entry point that can be run directly. This enables self-contained CLI tools as modules.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-010 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/feature/usage/cli_args_modspl_spec.spl` |
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

Tests embedding the cli keyword in mod.spl module files. When a module's
mod.spl contains a cli block, the module becomes an executable entry point
that can be run directly. This enables self-contained CLI tools as modules.

## Syntax

```simple
cli:
    verbose: false
    output: "result.txt"

fn main(args: CliArgs):
    if args.verbose:
        print "Verbose mode enabled"
    process(args.output)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/cli_args_modspl/result.json` |

## Scenarios

- defines cli in mod.spl
- generates CliArgs struct in module scope
- allows importing module functions alongside cli
- does not export CliArgs struct by default
