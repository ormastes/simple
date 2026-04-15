# Implicit Context Parameters

Tests implicit context parameters declared with `context val` and bound with `with_context`. Verifies that context variables work as module-level state shared across all functions, that nested function calls share the same context, that context can be swapped between loggers, and that the save-set-restore pattern correctly preserves outer context after inner scope execution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CTX-001 |
| Category | Language |
| Status | Active |
| Source | `test/feature/usage/implicit_context_spec.spl` |
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

Tests implicit context parameters declared with `context val` and bound with
`with_context`. Verifies that context variables work as module-level state
shared across all functions, that nested function calls share the same context,
that context can be swapped between loggers, and that the save-set-restore
pattern correctly preserves outer context after inner scope execution.

## Syntax

```simple
context val logger: TestLogger
with_context(logger: inner_logger):
_lex("x")
```
Feature 7: Implicit Context Parameters - End-to-End Tests

Tests demonstrate that context variables declared with `context val`
and bound with `with_context` work as module-level state shared across
all functions in the module.

The desugar pass has already transformed these patterns before the
runtime sees the code, so these tests exercise the generated output
directly using module-level var semantics.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/implicit_context/result.json` |

## Scenarios

- context variable is accessible in functions
- functions share the same context variable
- last logged message is from deepest function call
- context variable can be swapped for different loggers
- save-set-restore pattern preserves outer context
- nil context is default before any with_context
- multiple context vars are independent
- setting one ctx var does not affect others
