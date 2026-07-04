# Test runner: spec file killed at ~60s budget still prints PASS

**Date:** 2026-07-04
**Severity:** high (greenwashing — killed tests read as passing)
**Status:** open

## Symptom

A spec file whose cumulative runtime crosses the runner's ~60s per-file
budget is terminated mid-run (`Terminated`), yet the summary still prints
`PASS` for the file. `it` blocks after the kill point never execute and
their assertions are silently skipped.

## How found

Extending `test/01_unit/app/office/pptx_export_spec.spl` (9 OPC
package-building cases, ~63s baseline) with additional cases: the new cases
were killed mid-run while the file reported PASS. Verified by adding a
deliberate-fail case after the kill point — the failure was NOT counted.

## Workaround (in use)

Keep heavy spec files under the budget; put additional cases in a sibling
file (`pptx_layout_spec.spl` created for exactly this reason — see its
docstring). When extending any slow spec, re-run with a deliberate-fail
probe placed LAST in the file to prove the tail executes.

## Related

- Directory BATCH runs hang entirely (separate known runner/daemon issue).
- doc/08_tracking/bug/: see prior runner issues; test_result.md greenwashing
  fix (commit 1ae4c7d99fc) addressed per-describe sums, this is a different
  path (process kill, not sum).

## Next step

Runner should mark a killed spec file FAILED (nonzero exit propagated to the
file result) and print the kill reason. Likely site: per-file process budget
handling in src/app/test_runner_new/ (or its successor after the tree swap).
