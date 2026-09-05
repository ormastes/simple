# EasyFix lint-rule native execution hangs

Status: claimed; diagnostic follow-up deferred
Severity: P2 native tooling reliability
Owner: pure-Simple EasyFix rule execution path
Fix owner: unassigned outside the current Stage 4 type repair
Claimed source revision: uncommitted repair after `4c03aca49e6`

## Exact observation

Two executable versions of the focused Stage 4 lint-module contract compiled
successfully, then remained CPU-active without output or exit while invoking
the public lint rules. Attempt 1 used non-empty rule inputs; attempt 2 used
empty/early-return inputs. Attempt 2 was terminated by a 15-second timeout with
exit 124; both stdout and stderr were empty.

The same module's strict native HIR compilation is green after the canonical
integer-type repair. The current bootstrap regression therefore imports and
lowers the real rule implementation but does not execute this separately
claimed runtime defect.

## Required follow-up

1. Reduce the hang to a single public lint rule and distinguish call-entry,
   list-return, EasyFix construction, and shared line-context ownership.
2. Inspect staged-native text/list iteration only after the minimal reduction
   identifies it; do not assume the cause from the non-empty attempt alone.
3. Add bounded empty, non-empty, and multiline native regressions before
   marking fixed.

## Retained evidence

- `build/focused/stage4-fix-lint-module-hir/contract-attempt1.log`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt1.stdout`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt1.stderr`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt2.log`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt2.stdout`
- `build/focused/stage4-fix-lint-module-hir/contract-attempt2.stderr`
