# Bootstrap parser rejects labeled tuple return types
## Closed 2026-09-16 — Status SOURCE FIXED; focused regression passes 3/3 and 14/14; Stage3 rebuild acceptance pending

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Date:** 2026-07-17
**Status:** SOURCE FIXED; FRESH STAGE3 VERIFICATION REQUIRED
**Owner:** pure-Simple bootstrap parser

## Evidence

The bounded single-positional Stage3 rebuild reached phase 2 and failed on the
canonical `io_runtime.process_run` signature:

`(stdout: text, stderr: text, exit_code: i64)`

The tuple parser treated `stdout` as the first element type and then rejected
the colon. This blocks rebuilding the Stage3 artifact that must prove the
honest in-process SMF compile path.

## Source fix

`parser_parse_tuple_element_type` now accepts either anonymous `T` or labeled
`label: T` elements. Labels are intentionally discarded in the bootstrap tag
registry while the actual element types are retained; labels do not alter the
tuple ABI. The bootstrap source contract covers the canonical signature.

A focused interpreter-level regression now executes the current source parser
directly. It accepts the canonical three-label process result, accepts mixed
labeled/anonymous tuple elements, and rejects a label with no following type:
`3 examples, 0 failures`. This proves parser behavior without claiming that the
still-stale Stage3 artifact contains the fix.

The compile command also removes stale output before codegen and rejects a
success result unless a newly created SMF exists and is larger than the known
stub range (300 bytes).

After the GitHub rebase, a focused source-spec launch exposed one remaining
pure-frontend compatibility error before test execution: `lower_module` used
the reserved binding name `function`. It now uses `hir_fn`, matching the
neighboring bootstrap/function lowering fixes, and the Stage4 source contract
guards all three MIR-lowering files against regression. That contract also
escaped literal shell `${...}` braces so the current frontend does not treat
them as Simple interpolation; its final focused run passes 14/14.

## Remaining acceptance

1. Rebuild Stage3 with `SIMPLE_NO_STUB_FALLBACK=1` in a fresh bounded cycle.
2. Compile a print fixture through that Stage3 using both `--format=smf` and
   output-extension selection.
3. Require a nontrivial SMF, run it, and observe the exact print oracle.
4. Re-run the macOS live-window artifact gate with that verified Stage3.

No further rebuild was attempted in this session after the mandatory
three-cycle bootstrap cap. The repository-local Rust seed `check` command is
not independent evidence here: it delegates to the absent isolated
`bin/simple` and exits 127.


## Verification 2026-11-25 (work/p2w1-ak-20261125)

Source fix re-verified present on release/1.0.0 @ 3e04c857a56:
`parser_parse_tuple_element_type` at `src/compiler/10.frontend/core/parser.spl:820`
parses `label: T` tuple elements by discarding the provisional label type and
retaining `T` (lines 817-825 carry the exact comment describing this), and is
consumed by the tuple-type parse loop at lines 1398/1406. The remaining
acceptance (fresh Stage3 rebuild with `SIMPLE_NO_STUB_FALLBACK=1`, SMF print
oracle, macOS live-window gate) is bootstrap/deploy work, out of scope for a
doc-ledger pass on a Windows host with the pinned seed — left as recorded.
Row stays Closed.
