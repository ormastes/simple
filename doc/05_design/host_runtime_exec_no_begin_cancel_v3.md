# Qualified no-Host-BEGIN cancellation

This source implements the frozen interface proposed in
`host_runtime_exec_no_begin_cancel_v3_proposal.md`. It does not issue an exec
lease, observe native absence, tear down a container or release parent capacity.
Source and authored scenarios are **NOT_RUN** pending qualified execution.

The additive canonical `distributed_operation_journal_history_batch_v2` reuses
the exact existing operation-event parser/transition fold through a private
replay-snapshot reader. Normal replay and history qualification have one parser.
It records actual enclosing commits, initial admission and the last source/target
edge per operation, plus actual ancestor revision endpoints. Writer lease,
CURRENT and the complete indexed operation identity/envelope/state/outcome are
checked before returning a batch. V2 bytes, transitions, commit and owned cleanup
semantics are unchanged. History is in-process canonical data, never decoded
remote authority. It must match the actual current authority/head/sequence;
there is no generic stale-cache exemption.

One O(E+C) batch serves all children in a fixed guard projection. A receipt may
name an earlier real ancestor endpoint; unrelated appends do not invalidate that
receipt. An old supplied history batch is invalid after any mutation. The new
same-segment and multi-revision cases check commit-vector association explicitly.
Ordinary replay also constructs bounded history data through the shared fold;
the extra current-owner batch scan is constant-count, never per-parent replay.

The pure receipt archives original parent/child envelopes, original canonical
child packet digest, full scope, journal authority, actual pre-cancel endpoint,
separately signed parent cleanup proof and actual public policy/context. It has
no wait, absence or teardown fields. Policy source is bounded to 1 MiB and the
canonical receipt to 4 MiB. No decoder constructs permission or a native owner.

The cycle-free evidence module imports no Host root or capacity owner. It loads
the exact fixed private receipt, reuses actual child/parent/archive/native-creation
provenance, validates scope/digests and archived policy/signatures at the recorded
context. Optional missing receipt leaves a barrier; malformed present evidence
is an error. Current proof expiry is not substituted for historical validity.
Any contradictory delegation entry or indeterminate path state refuses proof.
Only an actual canonical admitted→cancelled edge, exact receipt outcome and
`admitted_sequence <= before_sequence < cancellation_sequence` with a matching
real endpoint qualify. Generic cancellation after executing/unknown cannot pass.

The producer accepts the current owned Host root and fresh separately signed
parent cleanup proof. It derives action `host_cleanup_v1` from the original parent
envelope, loads the protected installed public policy and verifies both SDK roles.
It requires the current exact admitted child and a charged parent in the same
current scope/native boot. Child launch proof is never cleanup permission.

The fixed private receipt is published before the outcome through the shared
publisher (dependency `17580ffb1d86f9fab328576628bb7d0f15eb94bd`). The final-fresh
callback uses an explicit read-only scoped Journal loan on the synchronous same
parent thread. It performs canonical lookup/current-owner checks only, with no
commit, close, HostRoot/Container capture, job transfer or retained callback.
After publication the producer refreshes authority and rechecks actual admitted
state before the existing canonical cancelled outcome commit. It returns the
updated owner and preserves stage metadata on every publication error.

Pending final receipts block BEGIN through landed interlock `bcbc6023804`.
Present, malformed or unknown fixed entry state is not clearance. Random private
stages do not establish a cancellation and are not scanned. If BEGIN occurred
after a failed attempt, the producer refuses cancellation and historical source
edge validation cannot qualify it. This follows the stable protected-parent
model, not a hostile-admin rename guarantee.

An existing receipt may resume only with byte-identical still-valid proof and
the same policy. Its Unix and same-native-boot monotonic accepted times are lower
bounds for current/rechecked clocks; no restamping is allowed. A fresh canonical
history batch proves its earlier endpoint for resume across unrelated appends.
Differing or expired proof remains a conservative refusal; bounded renewal is
not implemented. A cancelled row replay does not produce another mutation or
lease. Actual guard integration is owned separately by the Host guard lane.

Only the qualified child barrier can be omitted. A charged parent, unresolved
sibling or absent native cleanup proof cannot be released by this receipt.
The process-crash profile is preserved; private-file fsync adds no power-loss
claim to the existing WAL CURRENT publication. No Linux/Windows engine command,
Container API effect or new native backend is introduced here.
