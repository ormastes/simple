# Linux primary container geometry

Status: consumed source implementation, **AWAITING_VERIFICATION / NOT_RUN**.
The runtime campaign remains closed. This closes a Linux geometry source gap;
it does not qualify native behavior or complete Caret, Windows, or the broader
distributed execution acceptance plan.

## Endpoint contract and provider admission

The pinned Podman v5.2.5 route is
`POST /v5.2.5/libpod/containers/<full-native-id>/resize?h=<rows>&w=<columns>`.
It addresses the primary container, never an exec session or the attach helper.
The versioned route maps to `ResizeTTY`; its container branch invokes
`AttachResize` and returns HTTP 200 with an empty body. Its exec branch has a
different result and is not used. Sources:
[route registration](https://github.com/podman-container-tools/podman/blob/v5.2.5/pkg/api/server/register_containers.go#L1532),
[pinned handler](https://github.com/podman-container-tools/podman/blob/v5.2.5/pkg/api/handlers/compat/resize.go).
Reviewed source blobs are `cc1cc5e74df26941dbca3c837d4a2a02091144c6` and
`19ce87929cd10181be84358cc3a16a0d2b3121c6`, respectively. Current API documentation
agrees on the container route and `h`/`w` meanings; the pinned implementation
determines the empty-body response contract here.

The codec accepts only a full lowercase 64-hex container ID and fixed paths.
Columns are 1–512, rows 1–256, and area at most 60000. A fresh direct container
inspect requires exact ID, all five retained Simple runtime labels, running
status, `State.Running`, `Config.OpenStdin`, and `Config.Tty`. Strict bounded JSON
rejects duplicates and malformed/mistyped identity facts. Shared HTTP framing
retains existing exec/info behavior; primary resize is not added to the exec
request whitelist or relabeled as exec start.

The server loads optional `HOSTROOT/smux-primary-geometry-policy.sdn` once through
the existing no-follow bounded file owner. This is the existing canonical
`LinuxOciInstalledPolicyV3` schema, including its trusted local CLI policy,
socket path, service UID, and pinned API version. No wire request chooses these
values. Missing/unreadable configuration leaves geometry unavailable without
disabling Input. The common provider validates the policy against the actual
retained Linux provider baseline and session plan before connecting. Scripted,
containment, non-TTY, and unsupported-platform owners are refused.

## Common owner and exact authority

`container_primary_geometry_authorized_v1` borrows the canonical opaque primary
session. It correlates its exact current adoption, scope, provider/workload
identity and plan with a fresh independent Geometry lease. Input authority is
neither consumed nor substituted. The smux resolver additionally requires the
actual client attachment, current service/child incarnation, and executing
parent/helper journal rows. The trusted local issuer remains the authorization
owner; decoding request/lease metadata cannot create a native owner.

The common `primary_geometry_v1` API owns a separate finite HTTP continuation,
not another terminal session or reader. It retains no Host root or copied
provider writer. Each step receives the current common provider and canonical
pane session, matches the complete original request and lease, and refreshes
the provider baseline before allowing progress. Windows returns unsupported.

The Linux continuation performs info, container inspect, then resize, using
owned Unix connections. Actual Engine info must correlate with the retained
CLI baseline and installed policy. Each subsequent connection must match the
same observed UID, GID, PID, socket device and inode. These observations retain
the existing trusted-local-admin assurance; they are not hostile-same-UID or
strong process-incarnation authentication.

One step performs at most one bounded IO operation, with a 25 ms step deadline
capped by the original Geometry lease's absolute monotonic expiry. The native
socket owner checks that deadline immediately before sends. The Unix-clock
helper-admission send primitive is deliberately not used as a Geometry lease.
The persistent server serializes issuer changes and steps; it rechecks the
holder and adoption between fragments. Already submitted Engine work cannot be
rolled back by later revocation, so that boundary retains an uncertain outcome.

## Consumed smux protocol and lifecycle

The existing authenticated `runtime-primary-control-v4` route now dispatches
Geometry independently from Input. Resize requires an explicit positive
`attemptSequence`; offset and maxBytes remain zero. Legacy zero-attempt resize
still decodes but returns unsupported without an effect. Existing V1 control
requests keep their unsupported effect semantics. V4 discovery names the route
and the explicit-attempt requirement; configuration alone does not set a ready
geometry capability. A geometry reply's capability requires an actual recorded
endpoint acknowledgement and the current active lease.

The same control owner retains at most sixteen Geometry records separately from
the Input receipt registry. It reserves the full request digest, dimensions,
lease revision, session identity and explicit sequence before constructing or
stepping the common exchange. Periodic service turns progress at most one
retained Geometry exchange, rotating fairly across records. Inspection or an
exact request replay may also continue that same exchange; neither creates a
second request or connection attempt after a terminal outcome.

Every native connection and close uncertainty is returned into the canonical
record. Generic detach/attachment changes, selected-kind revoke, expiry, target
drift and explicit helper cleanup cancel invalid continuations before replying.
Cancellation closes the exact retained socket; it never sends a replacement
resize. Stop refuses pending exchanges or Unknown Geometry receipts. Input's
unknown outcome does not revoke or block a healthy Geometry lease, and the
inverse holds. Shared issuer guards apply equally to V1 and V4 issuance.

## Outcome and replay boundaries

Before the first resize send the native owner records `resize_attempted`.
Ambiguous bytes, timeout after submission, lost/malformed response or changed
peer therefore yield `unknown`, never a fabricated non-application result.
Only the exact retained HTTP 200/empty response records `acknowledged`.
Observing current dimensions does not prove that an ambiguous earlier request
executed. No inspection-based reconciliation is invented.

Failures before any resize send yield `rejected`. Close failure uses the same
production classifier: rejected before resize, unknown after an attempted
send, and an already acknowledged result remains acknowledged. Cleanup retains
the actual returned connection and may continue after lease expiry. A later
successful close cannot leave a terminal `pending` record without an owner.

Exact same-attempt/same-digest requests return or continue the retained record.
Changed dimensions/payload under that attempt and older sequences are refused.
Pending/Unknown outcomes prevent a new Geometry attempt, lease rotation or
session substitution for the same UID. Completed known outcomes may be followed
only by an explicit next sequence (or sequence one under a new valid lease).
Capacity refusal never evicts uncertainty. There is no automatic retry,
rotate-to-forget, or force-discard operation.

These records are process-local. The patch claims no restart-durable receipt
recovery, durable exactly-once resize, or reconstruction of a socket owner.
Service loss makes old process-local receipts unavailable; a new service cannot
reuse an old service-incarnation control target. Unresolvable Unknown records
can intentionally keep stop/rotation blocked pending future explicit operator
reconciliation. This is not a native qualification or full lifecycle completion
claim.

## Source evidence and remaining qualification

Eight HTTP/inspect scenarios and seven Geometry guard scenarios are authored,
and the existing V4 control-codec scenario now covers explicit resize attempts.
All remain **NOT_RUN**. They exercise production codecs, bounds, peer comparison,
deadline calculation, request/replay matching, failure disposition, and the real
pure issuer's selected-kind revocation/expiry rules. Metadata fixtures do not
create live sessions, socket owners, or positive cleanup proof.

Actual configured smux progression, native send deadlines, same-peer exchanges,
TTY resizing, injected partial-write/lost-response outcomes, native close-fault
retention and service-loss behavior are **NOT_COVERED** by these unit fixtures.
The modern SSpec acceptance inventory and required native fixtures are recorded
in `doc/03_plan/sys_test/container_primary_geometry_v1.md`. No docgen, runtime,
native smoke, performance, or broad acceptance pass is claimed.

The hot path uses fixed policy bytes, bounded in-memory issuer/journal checks,
one native IO step, and bounded response decoding. It does not spawn a CLI per
resize or repeatedly reload policy. JSON/HTTP parsing and the bounded control
sweep still need latency/RSS qualification; a 25 ms IO budget is not a measured
whole-server latency guarantee. Caret integration, Windows primary transport,
and the central distributed execution acceptance plan remain separate work.
