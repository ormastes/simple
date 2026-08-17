# Bug: audit analyzers contain an empty multiline `if` branch

- **ID:** audit_analyzer_empty_if_branch_2026-08-02
- **Date:** 2026-08-02
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Component:** `src/app/audit/{ffi_analyzer,sffi_analyzer}.spl`
- **Severity:** bootstrap diagnostic-sweep failure

## Reproduction

Focused checks of both analyzer entry files failed at the same source shape:

```simple
val todo_comment = if rt_calls.len() == 1:
else:
    "multiple-call message"
```

The parser correctly rejects the missing true-branch expression at `:` and the
following indent. This was source truncation, not a parser or sweep-harness bug.

## Fix

Restore a useful single-call diagnostic in both analyzers. The message includes
the concrete runtime call and its selected wrapper; the existing multiple-call
fallback remains unchanged.

## Regression coverage

`test/01_unit/compiler/parser_nonempty_if_assignment_spec.spl` executes the
same multiline assignment shape for both its single-item and multi-item paths.
Focused checks of both production analyzer files provide the exact reproduction
gate.
