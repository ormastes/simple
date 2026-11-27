# DAE-05 retention verification plan

Status: R3_DESIGN_REVIEW_REQUIRED / NOT_RUN, 2026-11-15. This is a test plan, not
an executable spec or generated manual. No new build, test, seed, native effect
or runtime restart is authorized in this design phase. See
[the frozen design](../../05_design/daemon_operation_retention_v2.md).

The following IDs refine the user-selected DAE-05 requirement; they do not mark
it complete or substitute checkpointing for retention/reclamation.

| Requirement | Required observation | Planned coverage |
| --- | --- | --- |
| DAE-05-A | One existing owner and publication boundary | Closed/stale/unowned journal rejects; second process cannot own parent.lock; distinct roots remain independent |
| DAE-05-B | Checkpoint preserves complete V2 state and history | Actual journal containing admitted, executing, outcome-unknown and each terminal state; compare every row/history/endpoint before and after checkpoint/reopen |
| DAE-05-C | CURRENT selects one complete recoverable revision | Inject failures before page, manifest, control and CURRENT publication and after CAS; reopen selects old or new complete state, never empty/admitted replacement |
| DAE-05-D | Bounded replay does not reset identity/sequence or lifetime policy | Explicit profile with tail bound below lifetime cap: fill tail, checkpoint, append below lifetime cap, reopen; global sequence increases and suffix resets; at lifetime cap checkpoint cannot admit an extra event; old reader rejects |
| DAE-05-E | Full/corrupt store blocks mutations/effects | Actual truncated, missing, changed/checksum-invalid object and manifest/page mismatch; page/count/byte/endpoint limits; failed CAS; exhausted disk/provider failure; external effect count stays zero |
| DAE-05-F | Runtime and receipt evidence survives compaction | Host no-begin cancellation keeps receipt.before_commit_digest and final edge; unresolved and terminal-but-pinned runtime evidence remains readable |
| DAE-05-G | Expired IDs cannot create new operations | Slice B: durable tombstone survives reopen, exact replay is EXPIRED, changed payload mismatches, direct commit refuses, independent new ID remains admissible if capacity permits |
| DAE-05-H | Expiry follows authoritative pin release | Slice B: pin each runtime/cleanup/capacity/reference/publication obligation; reject expiry until every one is authoritatively released; age/ack/cancel alone do not release |
| DAE-05-I | Dedupe horizon cannot silently forget IDs | Slice B: lifetime tombstones reach bound and block new admission; no eviction by age/session_generation; epoch-based reclamation absent until separately designed |
| DAE-05-J | Reclamation is exact and crash-safe | Slice C: object reachability/deletion manifest, interruption at each deletion point, reopen after partial GC, no domain evidence/locks/foreign-root objects removed |
| DAE-05-K | Durability claims match evidence | Process-crash matrix separate from power-loss matrix; absent file/directory flush evidence never produces power-loss PASS |
| DAE-05-L | Windows uses admitted retained-root capability | No new path CAS/native export; real publish/read/CURRENT CAS; missing delete capability explicitly prevents physical-GC qualification |
| DAE-05-M | Rollback/generation uncertainty blocks admission | Restore a consistent old CURRENT plus objects; change boot/provider identity; require managed-scope reconciliation, quarantine/retain charges for unmatched native resources, reject PID-only adoption |
| DAE-05-N | Corruption is quarantined and durability policy enforced | Preserve exact corrupt evidence and stable lock; no fresh-root recovery; reject requested power-loss guarantee without proven file/directory/publication flushes or prior approval of weaker policy |
| DAE-05-O | Profile opt-in and reopen enforce exact committed policy | Legacy no-profile behavior/default cap unchanged; no-profile checkpoint rejects without publication; invalid profile rejects before lease writes; checkpoint reopen missing/changed/unsupported profile rejects; no implicit lifetime-cap upgrade |

Planned executable files, after design approval:

- `test/01_unit/lib/common/task_runner/distributed_operation_checkpoint_v2_spec.spl`:
  strict SDN framing, ordering, bounds and independent golden bytes.
- `test/02_integration/lib/task_runner/distributed_operation_checkpoint_v2_spec.spl`:
  actual private filesystem, owned open/close, V2 transitions, checkpoint,
  corruption, tail limit and canonical history. No fabricated journal owner.
- Extend existing Host no-begin cleanup coverage only with that lane's ownership
  agreement. Its genuine receipt validation must accept unchanged lineage after
  checkpoint; a dictionary-equality-only test is insufficient.
- Future platform/system specs cover actual concurrent writers, crash points,
  disk exhaustion and qualified provider deletion. Windows adapter availability
  and native export approval remain prerequisites, not skips converted to PASS.

Freeze manual step labels before worker delegation: `Open the actual owned
journal`, `Commit representative V2 operation states`, `Capture canonical
history and pinned evidence`, `Publish the checkpoint through CURRENT`, `Reopen
and compare retained identities`, `Reject corrupt or exhausted storage before
effects`. Setup helpers: `checkpoint_open_owned_v2`, `checkpoint_close_owned_v2`,
`checkpoint_capture_history_v2`, `checkpoint_expect_same_projection_v2`.
Helpers must use real adapters and comparisons; any unfinished helper fails
explicitly. Authored manuals must say NOT_RUN until generated and independently
reviewed against executed evidence; executable specs never live under doc/06_spec.

Performance qualification records cold/warm open, hot lookup/commit latency,
checkpoint time and max RSS at representative envelope/endpoint/page limits.
No new numeric latency target is asserted without the selected baseline fixture.
Hot queries may use bounded pointer/owner checks, never replay the full snapshot.
Measure physical disk growth separately: Slice A performs no reclamation.

Execute each acceptance check once after an admitted runtime is available; fix
only real failures within the existing aggregate six-cycle limit. Source review
cannot discharge runtime, crash, Windows, fsync, performance or full DAE-05 gates.
