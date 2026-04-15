# Control Flow Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/interpreter/control_flow_spec.spl` |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/interpreter/control_flow/result.json` |

## Scenarios

- evaluates iterable before loop
- evaluates range expression
- creates new scope for loop variable
- binds loop variable for each iteration
- handles break with value
- handles continue signal
- checks condition before each iteration
- does not execute body if condition is false
- handles continue signal
- handles break signal
- breaks on Break signal
- can break with computed condition
- evaluates true condition
- evaluates false condition
- evaluates comparison expression
- executes then branch when true
- executes else branch when false
- matches tuple and binds variables
- uses wildcard for unmatched patterns
- matches array and binds elements
- handles array length mismatch
- nests for inside while
- nests if inside for
- combines match with for
