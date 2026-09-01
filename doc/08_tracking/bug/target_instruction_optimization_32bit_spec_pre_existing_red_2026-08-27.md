# target_instruction_optimization_32bit_spec pre-existing RED — std.spec does not export 'SPipe'

- Date: 2026-08-27
- Spec: `test/system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl`
- Status: OPEN (pre-existing at HEAD, proven below)

## Evidence
HEAD restore (`git show HEAD:<spec>`) run 2026-08-27:

    error: runtime: Module "std.spec" does not export 'SPipe'
    SPEC FILE VERDICT: ... outcome=ERROR declared>=29 executed=0 ...
    Results: 1 total, 0 passed, 1 failed

The spec imports `use std.spec.SPipe`, which the runner's `std.spec` module no
longer exports, so zero of the 29 declared scenarios execute. Same failure
shape as `test/unit/compiler/macros/macro_check_spec.spl` (also in this batch).

## Context
Recorded during the sspec modernization batch. The only edit applied here was
re-indenting misplaced `# @req REQ-TGT-*` comments into the `it` body
(TRC-003) — comment-only; the HEAD baseline above proves the red predates it.
Spec left RED per testing rules.

## Unblock condition
Either restore the `SPipe` export in `std.spec` or migrate the spec's import to
the current spipe entrypoint, then re-run.
