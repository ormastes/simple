# Orchestrator admitted architecture checkpoint

Status: **AWAITING_VERIFICATION**, 2026-11-07. This records the implemented
controller lane and remaining composition gaps, not a production-ready system.
The user requested test/documentation completion before further expansion.

## Implemented ownership

`common/contracts/orchestration/resource_v1` owns strict resource parsing and
quantity validation; `profile_v1` owns minimum/recommended/preferred resource
proposals. Pure proposals do not reserve capacity. Host capacity remains owned
by the host lane, with minima, no overcommit and exclusive-device constraints.

Placement, assignment and workload-fence contracts retain immutable workload,
controller epoch, host boot/provider generation and exact envelope identities.
`HostExecuteRequestV1` supplies bounded canonical framing. It contains untrusted
signed grant/approval values; decoding it never authenticates them. The host must
decode the actual retained Linux request, recompute its semantic digest, check
operation ID separately, and verify the exact action against its protected
authority. Semantic request digest is not a hash of raw retained SDN bytes.

The compiled app's `main -> command -> local_controller` path calls
`ControllerWorkloadStoreV1`, which owns one existing V2 operation-journal writer.
Desired source, policy and assignment objects are immutable content-addressed
objects beneath that journal. Replay preserves all original metadata domains and
rejects foreign operations. No parallel journal, scheduler or daemon loop was
introduced. TaskRunner retains parent-authoritative result acceptance.

Existing metadata replies remain V1 and explicitly unauthorized for execution.
The Caret client launches the configured controller process and validates those
identities; the compiled roundtrip has not run. Ten prototype execution methods
remain outside the admitted store. Generic create/bind still refuses bypass of a
UID already submitted as AgentSession.

## Agreed next composition, not implemented

The first signed dispatch target is explicitly `local-inprocess`: controller and
host have independently owned journals, but share a process and invoke the same
typed host command core and signed validators. It does not provide remote
process isolation or daemon liveness. An administrator must install immutable
controller epoch, host route and public-policy digest on the private metadata
root; request fields cannot replace them. Host enrollment and observed native
capacity/provider continuity remain separate host responsibilities.

Controller assignment and execution require distinct signed actions and current
protected authority. Host prepare and execute require their own distinct proofs.
Durable begin precedes effects; uncertain results retain the original operation,
assignment and charged capacity. A start observation is not completion, and only
host-owned native-absence evidence can justify resource release.

Local production grant, approval and authority-key expirations use Unix
milliseconds from an actual clock read. Preparation deadlines use monotonic
milliseconds plus boot identity. The unitless V2 verification API and historical
synthetic-clock fixtures are unchanged.

A bounded external host-process adapter was investigated but not implemented:
an unreaped owned process can require retaining its lease after cancellation.
No background adoption mechanism was confirmed. Discarding the lease, assuming
process exit proves cleanup, or spawning again after unknown outcomes is invalid.

## Acceptance boundary

The merged source slices are PR7544 (resource/profile), PR7568 (dispatch
prerequisites), and PR7578 (metadata CLI). A successful unadmitted resource probe
does not qualify any full-system path. Actual AgentSession source/image/invocation
resolution, signed controller dispatch, host execution, provider-native identity
and nonce inspection, Caret/Mux stream binding and parent result acceptance remain
unverified or unimplemented. Windows, macOS, FreeBSD, SimpleOS and cross-host
network acceptance remain open.

See the verification-wait plan for exact specs, manual provenance, prerequisite
failures and immutable source/evidence identities. Historical seed results in
`.spipe/simple_orchestrator/state.md` remain historical, without promotion.
