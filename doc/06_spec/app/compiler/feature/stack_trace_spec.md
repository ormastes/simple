# Stack Trace Specification

## At a Glance

| Field | Value |
|-------|-------|
| Source | `test/feature/dap/stack_trace_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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
| `result.json` | JSON artifact | `target/test-artifacts/feature/dap/stack_trace/result.json` |

## Scenarios

- pushes a single frame
- pushes multiple frames
- tracks frame information
- pops a single frame
- pops frames in LIFO order
- handles popping from empty stack
- starts at zero depth
- increments on push
- decrements on pop
- generates trace for single frame
- generates trace for multiple frames
- includes file paths in trace
- includes line numbers in trace
- returns empty trace for empty stack
- tracks recursive calls
- maintains separate frame instances
- handles frames with zero line/column
- handles frames with large line numbers
- handles empty function names
- handles empty file paths
- handles special characters in names
- handles deep call stacks
- efficiently pops many frames
