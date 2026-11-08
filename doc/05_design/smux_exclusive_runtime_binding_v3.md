# Exclusive local runtime binding

Status: source implementation; **AUTHORED_UNRUN**. This checkpoint composes
the real host, Container and terminal owners in one process. It does not
qualify a live attachment, an interactive terminal or independent host/smux
daemons.

## Ownership and deployment

`smux --serve-runtime-owner-file OWNER HOSTROOT` opens the installed protected
host root once and retains its sole capacity-journal writer. The canonical
retained private credential owner requires an effective-user-owned regular
no-follow 0600 input in an effective-user-owned 0700 directory, reached through
validated retained directory descriptors. `OWNER` remains immutable; startup
exclusively publishes `OWNER.ready` using kernel no-replace semantics. Its
exact newline-terminated record is `nonce address token diagnosticPid serviceIncarnation`.
A reconnecting client correlates nonce and service incarnation with authenticated
service responses; the PID is not ownership authority. A stale ready record is
refused, never overwritten or deleted. New startup uses a fresh input generation. Startup fixes
the host root, stream policy and fresh service incarnation. Wire requests
cannot override them. Concurrent host writers are rejected by the host owner;
separate host commands cannot run while this local composition holds the root.

The host functions verify grants, retain helper consumption and settle the
same journal. All container effects go through Simple Container API. The
Linux provider selects Podman; unsupported platform/transport combinations
are refused. Smux never builds engine arguments. Only the existing pane
poller reads an adopted stream. The full canonical group owner/reference
bundle is copied intact, including its optional V3 profile.

The text adapter uses the existing authenticated loopback protocol. It is not
a complete framed CoreMux protocol, OS peer authentication or remote host
authorization. The local token controls the local adapter; signed host proofs
remain necessary for helper effects. Required independent host-service IPC
and authenticated consumption/proof exchange are separate unfinished work.

## Public local flow

1. Before starting this exclusive process, retain the actual workload and
   authenticated parent budget through the host/controller paths. The target
   runtime must already exist; binding never creates or restarts it.
2. `runtime-binding-capabilities-v1` returns configured V2 protocol facts:
   planning supported, binding capability unresolved until a concrete plan,
   output-follow only, no input, geometry, interactivity or completion claim.
3. `create-runtime-target-v3 NAME` creates a vacant session/window/pane through
   the real metadata API without a shell. A unique existing vacant target
   with that name is reused; occupied or ambiguous targets are refused.
   `runtime-binding-target-v3 SESSION WINDOW PANE` returns exact service
   incarnation, epoch, revision and child incarnation.
4. `plan-existing-runtime-v3 TOKEN` decodes canonical base64url SDN containing
   the binding UID, workload/helper operation IDs, parent-budget digest and
   exact target fences. It reloads the installed policy, authenticated parent
   budget and protected retained workload, reinspects the provider, obtains
   the common output plan and checks actual plan-specific native capability.
   No helper lease is issued. The response contains the outer plan digest.
5. The same call publishes the full canonical `ContainerOutputPlanV2` at
   `JOURNALROOT/smux-binding-output-plans/SHA256(UID).sdn`. The external
   authority must read and sign those actual bytes; a digest response is
   insufficient to reconstruct a plan. The file is immutable 0600 planning
   data, not an authorization capability.
6. A trusted local authority stages the signed `HostHelperRequestV1` at
   `HOSTROOT/smux-helper-staging/SHA256(UID).request.sdn` and its canonical
   execution proof at the corresponding `.execution.sdn` path. These are
   untrusted signed inputs, read with bounded no-follow operations. No request
   chooses a staging path. `prepare-runtime-helper-v3 UID` invokes the actual
   host prepare function on the already-held owner and retains every turn.
   It reports reservation facts only, never a transport. Bind verifies the
   execution proof again through the actual host begin function.
7. `bind-existing-runtime-v3 TOKEN` reloads/recomputes the identical plan,
   verifies the helper packet and begins the exact helper operation. The host
   archives consumption before common Container opening. Every returned
   native outcome is retained. Ready means ownership is available; only a
   successful exact-fence pane adoption returns `adopted-opening`. It does
   not mean attach succeeded or that output/application readiness was seen.
8. Existing pane capture uses the sole reader. Normal viewer detach leaves
   the owner alive. Closing the attach helper is distinct from cancellation,
   termination or removal of the container. Input/paste/geometry remain
   unsupported for this output-only bundle.
9. `inspect-runtime-binding-v3 UID` reports retained state and reconciles
   failed/unadopted cleanup. It never cancels an adopted pane or opens another
   transport. After pane cleanup, it invokes host settlement, checks the
   exact operation/outer-plan/native identity ACK and clears pane ownership
   once. Cleanup success alone does not release capacity. This inspection is
   a lifecycle reconciliation operation, not a universally read-only query.

Prepare-only reservations can outlive process stop: like the finite host
prepare command, closing the writer preserves the durable charge. Once begin
may have committed, unresolved/native owners block stop until reconciliation.
An execution denial with the exact row still admitted is a prepared fact,
not an invented native owner that can never be cleaned up.

## Failure and restart

Every stateful host/provider turn replaces the retained owner before a reply
is encoded. Receipt-write failure preserves native cleanup ownership and
returns uncertainty. Same UID/different bytes is a conflict. Existing receipts
or committed journal rows never authorize a second begin/open. First binding
receipts stay immutable; later state comes from the host journal and retained
cleanup/settlement evidence.

Recovered bindings restore only the protected canonical group cleanup owner.
They cannot restore a registry reference, byte reader, PTY or interactive
readiness. A fresh process has a fresh service incarnation; old target fences
cannot authorize new adoption. This is cleanup-only recovery in an exclusive
local composition, not independent daemon restart support.

The existing server is synchronous and has short request deadlines. Host or
provider calls may outlast a client deadline. The client must preserve the
same UID and inspect uncertainty; no automatic bind retry or asynchronous
readiness is fabricated. A persistent host-service gateway remains required
for the independent deployment architecture.

## Requirements and verification

| Requirement | Source and authored evidence |
|---|---|
| REQ-SMUX-LOCAL-001: authenticate before parsing/effects | Actual server/client adapter; adapter unit spec and configured socket system spec |
| REQ-SMUX-LOCAL-002: exact immutable target and plan | Request/reply/target/policy codecs; immutable store specs; real target create/retry/refusal system path |
| REQ-SMUX-LOCAL-003: one native owner and one reader | Actual host/common open and pane adoption; existing owned-helper nonce/EOF spec; positive Container bind qualification outstanding |
| REQ-SMUX-LOCAL-004: cleanup and ledger release separate | Host settlement plus pure exact-ACK pane transitions; actual native/ledger positive qualification outstanding |
| REQ-SMUX-LOCAL-005: no duplicate effect on uncertainty | Retained first receipt, exact host begin and consumed-plan archive; full crash/replay system matrix outstanding |
| REQ-SMUX-LOCAL-006: preserve platform/authority boundaries | Output-only native capability; no engine calls in smux; stdin/resize and independent gateway remain unsupported here |

All new Simple scenarios, compiled process tests, doc generation and full
regression suites remain **NOT_RUN**. Pure codec/metadata assertions are not
native attachment or settlement evidence. The configured socket scenario
requires actual compiled binaries, protected enrolled root and native broker
resources; missing prerequisites fail rather than skip/pass. Full positive
acceptance additionally needs a real signed-plan authority fixture, fresh
workload output, independent Container inspect, EOF/cleanup proof and exact
host journal release. No production-readiness PASS is asserted.

## Startup and shutdown ownership

Configured startup consumes `HostLocalRootOpenV2`, including its canonical
partial journal cleanup capability. A policy failure closes through the owned
host API and retains every returned cleanup state. Only `Released`, `closed`,
no cleanup capability and an empty error establish host release. Unknown, stale
or consumed-error states cannot be converted into a new writer or a successful
stop. Native credential close similarly reports consumed uncertainty without
retrying an old descriptor.

If startup has an unresolved host cleanup owner after one compensation attempt,
the same process keeps a cleanup-only authenticated listener and reports
`owner cleanup pending`; it publishes no successful ready record. Every command
except authenticated stop is refused. Normal stop releases the real host writer
and native credential owner before it acknowledges listener shutdown. This is
still exclusive in-process recovery, not an independent service restart protocol.

The configured socket scenarios now inspect the immutable five-field ready
record and correlate its incarnation with actual capability/target responses.
Legacy four-field owner-file scenarios retain their existing behavior and gain
no configured host authority. These scenarios and startup propagation specs are
AUTHORED_UNRUN until a qualified runtime is allocated.
