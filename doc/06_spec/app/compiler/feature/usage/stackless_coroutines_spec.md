# Stackless Coroutines Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/usage/stackless_coroutines_spec.spl` |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/stackless_coroutines/result.json` |

## Scenarios

- creates generator that yields values
- generator evaluates lazily
- preserves state across iterations
- generator with multiple yields
- defines async function
- handles async computation
- returns error from async
- chains async operations
- manages resources in async context
- yields single value
- yields multiple values
- yields computed expressions
- yields based on conditions
- runs multiple generators
- interleaves coroutine execution
- avoids stack allocation overhead
- handles many coroutines
- creates coroutine in initial state
- coroutine starts in suspended state
- completes after yielding all values
- cleanup happens on completion
- transitions from created to running
- transitions through suspend and resume
- transitions to completed
