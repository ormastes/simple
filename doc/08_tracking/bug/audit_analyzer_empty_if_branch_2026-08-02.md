# Bug: audit analyzers contain an empty multiline `if` branch

- **ID:** audit_analyzer_empty_if_branch_2026-08-02
- **Date:** 2026-08-02
- **Status:** FIXED
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

## Phase3 recurrence (2026-10-25)

Frozen source `46772223a7c`, producer `991be8f97493426d22fa944bd212afa22487bb22b31d2a6ea0ab95e8b4e05974`,
module-diagnostics attempt `3cx5IX`, rows 16/17 repeated this source truncation:
`sffi_analyzer.spl:213:17` and `ffi_analyzer.spl:213:17`, `expected Indent, got else`.
The exact single-call strings from donor `e01ae78e5ea65ebbb4a98416c86db2b73d2c94a2`
are restored again. Both branches require an expression; no valid compact syntax
was rewritten and no parser relaxation is warranted. The existing focused
parser regression remains the acceptance gate for this assignment shape.
