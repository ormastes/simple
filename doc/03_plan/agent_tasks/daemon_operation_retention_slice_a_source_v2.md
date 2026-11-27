# DAE-05 Slice A source continuation handoff

Historical R1 handoff. The remainder records the frozen R1 source, not the
current worktree. Current owner-health implementation and evidence limits are
in [the R2 handoff](daemon_operation_retention_owner_health_v2.md).

Status: **SOURCE_BLOCKED / NOT_RUN**, 2026-11-15. Independent Astra review is
required; no implementation/verification/release completion is asserted.

Worktree: `/home/yoon/dev/simple-collected-stream-null-20261114`.
Branch: `work/daemon-retention-design-20261115`. Root owns integration and landing.
The approved R3 design and its original planning files were preserved bytewise.
Existing six-file Windows storage foundation is a separate dependency, with
[its provenance](daemon_operation_retention_foundation_v2.md); it was not edited
or reclassified as this continuation's work. Its native exports remain unapproved.

## Preserved implementation and new delta

The restored source already implemented the explicit retention profile, history
contract relocation/re-export, bounded canonical checkpoint codec/schema,
generic WAL checkpoint control/CURRENT CAS, owner checkpoint publication, and
checkpoint-plus-suffix replay through the existing transition validator. It
retains complete rows/history/endpoints and preserves the absolute lifetime cap.
It does not auto-enable a production profile or introduce another domain writer.

This continuation changed exact control-byte accounting in
`distributed_operation_checkpoint_v2.spl`: the actual manifest digest selects
canonical SDN quoting, so the encoder charges its exact control after hashing
the manifest; the decoder computes the same size from actual manifest bytes.
The previous placeholder `a` digest underestimated all-decimal digest quoting.
All objects are still checked against the aggregate limit before publication.

The continuation added six pure codec cases with independently spelled golden
bytes and boundary assertions, extended the actual-owned integration source to
twelve scenarios, and authored matching unit/integration manuals. Counts are a
source inventory only, not registered/executed test counts. One integration
scenario is an explicit regression assertion for the unresolved blocker below.
No fake owner, checkpoint backend, native effect or placeholder pass was added.

## Release blocker: integrity failure is not sticky for copied owners

In `distributed_operation_journal_v2.spl`, `history_batch` can discover a corrupt
historical snapshot page and return an integrity error. The journal is a copied
value; no canonical shared health owner records that discovery. A subsequent
lookup/commit validates owner and CURRENT only. When CURRENT is an ordinary data
revision over a checkpoint, those checks do not read older snapshot pages. Even
if corrupt bytes are restored, the design requires the affected generation to
remain quarantined until authoritative close/reopen. Current source permits a
terminal commit through a prior copy, violating the R3 contract.

The final integration scenario opens a real owner, admits/checkpoints/begins an
operation, copies its executing owner, corrupts a committed historical page,
requires actual history replay to return its checksum error, restores the exact
page bytes, then requires copied-owner terminal commit to fail without changing
CURRENT. Source inspection predicts failure of that required assertion today.
It has not been run and must not be marked passing, ignored or removed merely
to obtain a green suite.

## Smallest ownership change proposed for Astra approval

No safe sticky-health implementation was added in this continuation. The
reviewed next proposal is one intentional process-lifetime existing
`mutex_new_gate(0)` protecting a bounded private journal health registry; no
per-owner mutex allocation/destructor and no path-derived authority. A slot
binds the actual `FileLockOwnerV2.token` or retained
`WindowsJournalStoreV1.same_owner` generation, a nonreused logical ID, first
bounded integrity reason/exact failing digest, and an operation ticket.

- Reserve within a fixed bound before acquiring native resources, or preserve
  actual typed cleanup if registration fails. Refuse logical-ID exhaustion;
  do not recycle an ID into stale copied values. Quarantined and cleanup slots
  count toward the bound. All accesses use the same gate.
- Bind native identity once before Ready and enforce one live slot per actual
  native generation. In particular `open_windows_v3` receives an existing store:
  reopening that same live store/nonce cannot clear poison or close a borrowed
  existing authority on duplicate refusal. A fresh healthy owner needs actual
  native close/reacquisition.
- Preserve the slot through every constructor, commit/checkpoint result and
  typed open-cleanup carrier. Missing, stale or foreign IDs fail closed, never
  lazily register. Newly owned/profiled journals cannot bypass health with nil;
  legacy unowned checkpoint remains unsupported.
- Record the first stored-integrity/projection failure before returning it.
  Stale copied revisions, missing operation IDs and caller validation failures
  do not poison a healthy canonical generation. Preserve the exact corrupt
  objects/CURRENT; do not rename locks or create an empty root.
- A health check followed by I/O is insufficient if another alias can poison
  meanwhile. Either enforce a proved existing single-operation/thread contract,
  or use a per-slot operation ticket under the same gate to reject concurrent
  alias access. Public entrypoints acquire once; nested lookup/history helpers
  reuse that ticket. Typed cleanup follows the same serialization. No native
  I/O/domain-lock acquisition occurs while the global metadata gate is held.
- Retire only the exact slot after confirmed native Released/ConsumedError or
  Windows released. Retained/Unknown close keeps it. Old cleanup cannot erase a
  new generation; copied close cannot clear live poison. Handle registration,
  close, concurrent alias and late-poison races with actual owner regressions.
- Gate acquisition/unlock failure never means healthy and never authorizes
  slot removal. Refuse further operations while preserving actual owner/cleanup
  obligations; post-acquisition registration failure retains the native owner.

This introduces shared mutable metadata, so the parallel-ownership rules apply.
Independent Astra specifically requested generation uniqueness, exact cleanup,
normal-error classification and serialized copied-owner access. Existing mutex
gate reuse is a candidate mechanism, not evidence that these semantics are
implemented or qualified. A bare bool field, unsynchronized globals or untyped
manual AtomicBool lifecycle is insufficient.

## Evidence limits and remaining objective

Canonical `bin/release` is absent. No build, test, native/runtime execution,
Rust-seed fallback, engine effect, stage/commit/push/rebase/branch switch or
bootstrap restart was performed by this continuation. The aggregate exhausted
campaign remains stopped. Runtime syntax/type/link checks, SPipe generation,
manual maintenance/independent acceptance, branch coverage, core/MCP smoke,
Windows/provider/crash/disk-full/power-loss matrix and performance remain
**NOT_RUN**. Source review and whitespace checks cannot discharge them.

Full DAE-05 remains open: owner-derived pins, durable response expiry and
lifetime dedupe tombstones, exact physical GC, rollback/provider reconciliation,
provider deletion capability and platform qualification are still required.
Slice A does not reclaim disk, increase the lifetime cap, or imply power-loss
durability. Root must obtain independent Astra source/architecture review before
accepting even the bounded Slice A implementation.
