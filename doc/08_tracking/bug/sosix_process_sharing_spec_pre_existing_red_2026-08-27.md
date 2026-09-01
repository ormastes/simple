# sosix_process_sharing_spec pre-existing RED — `sosix_dataset_active` not found

- Date: 2026-08-27
- Spec: `test/system/app/os/feature/sosix_process_sharing_spec.spl`
- Status: OPEN (pre-existing at HEAD, proven below)

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
