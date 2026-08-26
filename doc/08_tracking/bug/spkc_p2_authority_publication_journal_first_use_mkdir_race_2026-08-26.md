# SPKC P2 authority-publication journal durable replay and reclaimer races

Status: OPEN (P1)

## Defect

`AuthorityPublicationJournalV1` is **NON-ADMITTED**. Four release-blocking
defects remain in one durability/authority boundary:

1. On a fresh ledger, two independent publisher processes can both observe
   missing ledger ancestors. A non-recursive `mkdir` by the loser then raises
   `EEXIST`, rather than being treated as a raced-but-verified creation.
2. `_open` can project persisted state without first verifying the exact closed
   canonical-input schema and canonical bytes. A persisted `schema_version`
   change from 1 to 2, or an added field, must be denied before projection; it
   must never be sanitized, defaulted, or accepted.
3. A reclaimer using `O_EXCL`/hardlink ownership must not let an `EEXIST`
   contender unlink another live reclaimer's claim. Removal requires the exact
   observed claim identity and ownership revalidation, not a path-only retry.
4. Receipt liveness must reject a PID that is not a positive safe integer
   before any call to `process.kill`. In particular, `process.kill(0, 0)`
   probes the caller's process group and can incorrectly certify an arbitrary
   lock as live. A corrupted receipt must fail closed into the exact durable
   `O_EXCL` reclaim protocol (or a reported unrecoverable state), not loop for
   an arbitrary 1,000 attempts or treat malformed PID data as authority.

These are authority, correctness, and availability failures. Weakening
ownership, canonical verification, or durability to retry them is prohibited.

## Reproduce contract

Start from PR baseline `ca518eef24a25871dd8125a08f24efe980205510` in a fresh
isolated worktree and an absent journal ledger. Use a two-process ready/start
barrier so both independent Node processes first create the same ledger
ancestry, then attempt the normal durable publication/lock path. The P2 draft
can fail with `EEXIST` while constructing a parent directory. Separately,
persist a canonical v1 record, mutate only `schema_version` to 2 and then add
one unknown field, and prove `_open` rejects both before it returns any
projected state. Finally, force two reclaimers to race for a stale lock: one
must win a durable claim, and the losing `EEXIST` contender must preserve that
live claim exactly. An in-process race, pre-created ledger, timer-only probe,
or a parser that repairs malformed state is not a reproducer.

Also persist or arrange a stale receipt with each of `pid: 0`, `pid: -1`, a
non-integer numeric PID, and a PID above `Number.MAX_SAFE_INTEGER`. Instrument
or substitute the liveness seam to prove no case invokes `process.kill`.
For a corrupted owner receipt, run two independent reclaimers under the normal
`O_EXCL` protocol and prove exactly one claimant can acquire ownership without
an arbitrary retry-bound timeout; the loser must preserve the winner's durable
claim.

## Safety invariant

A visible lock must have a durable owner receipt. Stale recovery may remove
only the exact observed owner/lock identity after revalidation: it must never
use ownerless recovery, path-blind unlink, public journal/permit state, or an
in-memory lock. Every newly created ledger ancestor, including `shared/`,
`shared/spipe/`, and the journal root, must be fsynced before acknowledgement.
Persisted canonical input is a closed schema: its declared version, complete
field set, canonical byte representation, and bound replay identity must all
verify before `_open` constructs a projection. A reclaimer claim is likewise a
durable identity, not merely a pathname; an `EEXIST` loser may observe and
report it but may not delete it without exact ownership revalidation.

PID liveness is advisory only after receipt parsing passes: valid means an
integer in `[1, Number.MAX_SAFE_INTEGER]`. Every other PID is invalid and must
be denied before signaling. Corruption is not evidence that a lock is live,
and it is not permission for path-blind deletion; recovery must retain the
same exact-identity, exclusive-claim protocol and terminate with a durable
outcome rather than a fixed retry-count timeout.

## Accepted prior evidence and boundary

P1 is accepted for closure-branded target inventory/permit selection and
canonical replay-envelope normalization. Cycle 3 also produced useful
non-admission evidence: the journal constructor/owner is lexical-private,
the absent-root process test sequences the genuine parent-creation path, and
independent processes deny replay divergence. Those positives do not admit P2:
the durable lock/reclaimer boundary still has all four defects above. Earlier
P2 focused/package tests, independent process-race coverage, and
SIGKILL/restart probes remain non-admission evidence. No P2 source repair is
authorized in the capped session.

## Fresh-session entry point

```sh
git worktree add --detach /tmp/spkc-p2-journal-repair ca518eef24a25871dd8125a08f24efe980205510
cd /tmp/spkc-p2-journal-repair/examples/05_stdlib/spipe
node --test test/unit/target_inventory_store_test.js
```

The fresh lane must first add all combined reproducers: barrier-based
fresh-ledger creation, v1-to-v2/extra-field closed-schema rejection before
projection, two-reclaimer `EEXIST` claim preservation, and PID-validation plus
corrupted-receipt exact-`O_EXCL` recovery. Then run the combined reproducers
once after the repair and submit the exact-scope diff for an independent
highest-capability review. A passing focused command alone is not admission
evidence.

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
4. `_open` rejects, before projection, a byte-valid persisted v1 record whose
   `schema_version` is changed to 2, and rejects one with a single extra field.
   Neither case may be sanitized, defaulted, or replayed.
5. Two independent reclaimers race on a stale lock. After one wins a durable
   `O_EXCL`/hardlink claim, the losing `EEXIST` contender neither unlinks nor
   replaces that live claim; recovery remains bound to exact claim identity and
   ownership.
6. Liveness rejects PID `0`, negative, fractional, non-numeric, and
   non-safe-integer values before any `process.kill` call. A corrupted receipt
   enters the exact durable exclusive-claim outcome path: concurrent
   reclaimers have one owner, the loser preserves it, and neither path uses an
   arbitrary 1,000-attempt timeout.

No source is admitted until one fresh lane passes all six cases together,
including the earlier SIGKILL/restart recovery case, and an independent
highest-capability review accepts the exact-scope diff.

Cross-links: [agent remediation order](../../03_plan/agent_tasks/spipe_knowledge_compiler.md#wave-5-admission-remediation-execution-order-2026-08-26)
and [W5A publisher gates](../../03_plan/sys_test/spipe_knowledge_compiler.md#224-ordered-remediation-gates-blocking-test-execution).
