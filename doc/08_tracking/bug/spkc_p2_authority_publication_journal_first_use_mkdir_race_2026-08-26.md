# SPKC P2 authority-publication journal first-use mkdir race

Status: OPEN (P1)

## Defect

`AuthorityPublicationJournalV1` is **NON-ADMITTED**. On a fresh ledger, two
independent publisher processes can both observe missing ledger ancestors. A
non-recursive `mkdir` by the loser then raises `EEXIST`, rather than being
treated as a raced-but-verified creation. This is a first-use correctness and
availability failure; weakening ownership or durability to retry it is
prohibited.

## Reproduce contract

Start from PR baseline `ca518eef24a25871dd8125a08f24efe980205510` in a fresh
isolated worktree and an absent journal ledger. Use a two-process ready/start
barrier so both independent Node processes first create the same ledger
ancestry, then attempt the normal durable publication/lock path. The P2 draft
can fail with `EEXIST` while constructing a parent directory. An in-process
race, pre-created ledger, or timer-only probe is not a reproducer.

## Safety invariant

A visible lock must have a durable owner receipt. Stale recovery may remove
only the exact observed owner/lock identity after revalidation: it must never
use ownerless recovery, path-blind unlink, public journal/permit state, or an
in-memory lock. Every newly created ledger ancestor, including `shared/`,
`shared/spipe/`, and the journal root, must be fsynced before acknowledgement.

## Accepted prior evidence and boundary

P1 is accepted for closure-branded target inventory/permit selection and
canonical replay-envelope normalization. Earlier P2 focused/package tests,
independent process-race coverage, and SIGKILL/restart probes remain useful but
non-admission evidence because this fresh-directory race remains. No P2 source
repair is authorized in the capped session.

## Fresh-session entry point

```sh
git worktree add --detach /tmp/spkc-p2-journal-repair ca518eef24a25871dd8125a08f24efe980205510
cd /tmp/spkc-p2-journal-repair/examples/05_stdlib/spipe
node --test test/unit/target_inventory_store_test.js
```

First add the barrier-based fresh-ledger reproducer, then run it once after the
repair and submit the exact-scope diff for an independent highest-capability
review. A passing focused command alone is not admission evidence.

## Minimal affected files

- `examples/05_stdlib/spipe/src/storage/authority_publication_journal.js`
  (the required W5A-J canonical durable owner; create it if absent)
- `examples/05_stdlib/spipe/src/core/knowledge_compiler_commit_publisher.js`
  (the current composition-root seam, not a replacement journal owner)
- `examples/05_stdlib/spipe/test/unit/target_inventory_store_test.js`

## Fresh acceptance cases

1. Two independently launched processes simultaneously create an absent nested
   ledger; equal canonical replay inputs obtain the same idempotent result,
   while changed revision/expected IDs/deltas deny before publication; neither
   path may produce an unhandled `EEXIST`.
2. Kill the owner during first creation and restart independently; recovery
   exposes only the prior complete or one complete new state and never deletes
   a concurrently replaced live lock.
3. Fault-inject every first-use parent creation and verify file plus every new
   ancestor-directory fsync in the durable chain before acknowledgement.

Cross-links: [agent remediation order](../../03_plan/agent_tasks/spipe_knowledge_compiler.md#wave-5-admission-remediation-execution-order-2026-08-26)
and [W5A publisher gates](../../03_plan/sys_test/spipe_knowledge_compiler.md#224-ordered-remediation-gates-blocking-test-execution).
