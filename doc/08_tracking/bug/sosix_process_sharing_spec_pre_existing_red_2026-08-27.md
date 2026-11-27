# sosix_process_sharing_spec pre-existing RED — `sosix_dataset_active` not found
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-08-27
- Spec: `test/system/app/os/feature/sosix_process_sharing_spec.spl`
- Status: SUPERSEDED 2026-11-11 — reconciled by the owning module's current
  API; spec verified green 6/6 at release tip. See the dated addendum below.

## Evidence
HEAD restore (`git show HEAD:<spec>`) run 2026-08-27:

    Results: 6 total, 0 passed, 6 failed

Every scenario fails with `semantic: variable 'sosix_dataset_active' not found`
(first failing scenario: "should seal a dataset before it becomes readable
shared data").

## Context
Recorded during the sspec modernization batch (mirror score <=80 triage). The
spec's scenarios have real oracles; the referenced variable is missing from the
module the spec imports, so the whole file is red independent of any
modernization edit. The only edit applied in this batch was re-indenting
misplaced `# @req REQ-SOSIX-SHARE-*` comments into the `it` bodies (TRC-003);
it is comment-only and cannot change behavior — HEAD baseline above proves the
red predates it. Spec left RED per testing rules.

## Unblock condition
Restore/export `sosix_dataset_active` (and whatever sibling symbols the sealed
dataset scenarios reference) from the sosix sharing module, or reconcile the
spec with the module's current API.


---

## Addendum 2026-11-11 — lane runner7: SUPERSEDED (spec green at release tip)

Re-ran the filing spec on the refreshed Windows seed (`bin/simple.exe` at HEAD
`68ab3383080f`, 2026-11-11):

```
SIMPLE_LIB=src bin/simple.exe test test/system/app/os/feature/sosix_process_sharing_spec.spl --mode=interpreter --no-cache
SPEC FILE VERDICT: ... outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
Results: 6 total, 6 passed, 0 failed
```

The unblock condition is satisfied: `sosix_dataset_active` and every sibling
symbol the scenarios reference now exist in `src/os/sosix/share.spl` (module
arrived in its current form via merge `9e7e7a526edb`, PR #7597, 2026-11-07;
module-level globals carry explicit defaults per the in-source note referencing
`doc/bug/sosix_sharing_uninitialized_globals_2026-10-29.md`). The spec imports
the API unchanged; no spec edit was needed. Verdict: SUPERSEDED — absorbed by
the owning sosix module's current API, verified green 6/6.
