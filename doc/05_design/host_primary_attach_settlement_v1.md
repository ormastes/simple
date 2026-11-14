# Host primary attachment cleanup and settlement

Status: source implementation; runtime qualification NOT_RUN. This advances
the Host prerequisite for primary terminals. smux/Caret migration and Windows
primary transport remain incomplete.

The primary opener previously retained charged helpers and actual sessions or
cleanup carriers, but Host completion only recognized output-follow evidence.
The new primary settlement module composes the existing terminal cleanup/reap
owner, canonical broker proof, capacity journal, and shared settlement ACK.
It introduces no signer, ledger, execution grant, or parallel state machine.

## Separate lifecycle actions

`host_primary_attach_cleanup_v1` is explicit cancellation/cleanup of the helper
transport before pane adoption. It never stops or destroys the workload
container. The exact owned session or cleanup carrier is matched against its
retained primary plan and real broker metadata before cleanup. Failure returns
the entire retained turn. Successful cleanup preserves the updated session or
removes the retired descriptor reference from the cleanup carrier; the native
cleanup owner and charged reservation remain retained.

An adopted session is refused by this Host cleanup entrypoint. The canonical
terminal owner must clean it and return the updated session for settlement.
Value copies are not mechanically revoked; callers must transfer the canonical
session and must not keep an independently usable Host copy after adoption.

`host_primary_attach_settle_v1` is observation-only. It requires existing exact
broker terminal proof before retirement; it never invokes cancellation. An
adopted session must already carry the terminal owner's native-cleaned state.
The existing terminal reap operation validates immutable helper/lease domains,
retires the exact native owner, and collects canonical reap evidence. Its
updated session is stored before checking any later error. Cleanup-only
carriers use the same proof-before-retirement and canonical reap mechanisms.

Settlement publishes primary evidence, then uses the shared helper commit
function. That function independently reads the capacity owner's exact evidence,
derives ACK metadata from those bytes, invokes `host_capacity_owner_settle_v1`,
and checks the completed journal digest. A completed operation can reconcile
its ledger using the same existing transition. The newest journal owner is
returned even if a later check fails. A successful cleanup flag or caller
receipt can never release capacity.

## Exact evidence domains and recovery

The capacity evidence hook now selects exactly one consumed domain:
`host-helper-stream-consumed` or `host-helper-stream-primary-consumed`.
Both present is an error, including a malformed second marker. Neither present
is an error. A corrupt selected domain is never a fallback to another domain.
Presence uses `path_entry_present` with explicit failure propagation and real
directory checks; uncertain IO and dangling entries are not interpreted as
absence. This retains the existing trusted stable-parent filesystem contract.
The archive selector requires the trusted absolute, dot-free journal-root
spelling used by HostLocal; it does not canonicalize arbitrary relative roots.

Primary native archives bind the consumed plan and operation to the exact
canonical broker claim and profiled launch. Missing archive metadata can be
recovered only from that consumed broker root. Partial, conflicting, symlink,
or dangling archives are preserved and refused. Recovery reconstructs cleanup
metadata only, never a live session, descriptor, reader, or workload identity
from a helper PID.

`host_primary_attach_recover_v1` obtains the exact original operation from the
current journal, matches the retained intent/plan host and fence to the current
capacity owner before archive repair, and returns metadata only. `host_primary_attach_settle_recovered_v1`
refreshes and matches the retained operation, primary plan, consumption digest,
and full native launch before checking actual terminal proof. This supports
retry after host loss between native retirement, tree-reap publication,
settlement publication, and journal commit. Missing proof preserves the charge;
neither recovery nor recovered settlement reconstructs the vanished helper
lease or terminal session. Live and recovered paths share primary evidence
publication and the same capacity commit mechanism.

Primary settlement evidence requires an already stored canonical tree-reap
receipt, the exact helper lease, and actual broker cleanup proof. The capacity
hook revalidates these independently. Output-follow uses its unchanged evidence
schema and the same shared commit/ACK mechanism.

## Verification limits and next integration

Nine source-only evidence scenarios use signed-data/admission fixtures and the
actual journal/file APIs. Synthetic broker claim/request metadata is used only
to test refusal. Scenarios cover output compatibility, missing/corrupt/dual
domains, exact native metadata, missing/partial/symlink archives, altered native
identity/template, and forged settlement without terminal proof. They assert
unchanged journal and ledger revisions and preserved CPU/memory capacity.
The metadata-recovery scenario also covers a missing native archive with actual
claim/request metadata present, then missing-proof settlement and altered
consumption-digest refusal. Mismatched capacity host/authority/boot/provider
facts must fail before creating the missing native archive.

All runtime execution is NOT_RUN under the existing six-cycle campaign cap.
Positive native cleanup, actual descriptor retirement, post-retirement failure
retention, successful/replayed live or recovered settlement, adoption handoff, and performance are
NOT_COVERED by these evidence tests. Source review does not replace them.

smux must migrate planning, bind, retained state, pane adoption, sole-reader
output, separately authorized input/geometry, cleanup, and settlement together.
Its current V3 wire requires output-follow semantics, so primary support needs
a versioned or negotiated extension. Caret and Windows Docker primary support
cannot be claimed from this Host prerequisite.
