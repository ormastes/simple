# Remote completion authority — RUN-01 / RUN-02

Status: source implementation, AWAITING_VERIFICATION. No native execution,
cross-host success, generated-manual quality, branch coverage or release admission
is claimed. The existing local-only `database_session.spl` guard remains intact.

## Authority and ownership

The original approved `OperationEnvelopeV2` binds the exact encoded BuildTask.
That task binds producer, source, toolchain, arguments, input/output closure and
attempt. Its `remote-policy/<task-id>.sdn` input additionally binds host,
assignment digest, controller epoch, operation ID, build/test kind, transfer
budget, toolchain file inventory and expected test identities. Each toolchain
file is itself a declared input. New remote policies define toolchain identity
as the canonical ordered inventory digest.

The protected controller/host composition supplies current authority keys,
policy/revocation/session state, observed environment and active assignment.
These values are never decoded from the completion bundle. Grant issuer,
human approver and execution-host keys have separate roles and public keys.
The completion verifier revalidates the original grant and approval and the
host's current scoped enrollment before checking its Ed25519 signature.

A signed completion binds the exact request/grant, task, host, operation,
assignment/fence, result/process payloads, output inventory, tests, cleanup,
timestamp and key revision. A signature establishes the enrolled host's claim;
the receiving parent separately hashes the actual transferred binary buffers,
validates process/log consistency and exact output/test inventories. Neither
exit zero, a signed digest, a start observation nor an unbound reap file suffices.

## Components

| Owner | Responsibility |
| --- | --- |
| `remote_context_v1` | Protected current authorization, environment, resource and fence binding |
| `remote_authority_v1` | Canonical completion codec and original grant/approval plus host signature verification |
| `remote_evidence_v1` | Immutable policy, actual byte hashes, exact outputs and exact passing test inventory |
| `remote_capture_v1` | Bounded regular/no-follow reads from a private local staging root |
| `remote_host_v1` | Native-domain local start/collect owner; never signs a caller-supplied completion |
| `remote_bundle_codec_v1` | Bounded canonical chunked binary transport; decoding provides no authority |
| `remote_session_v1` | Serialized parent cancellation, journal admission, recovery and output publication |
| `remote_test_report_v1` | Pinned TraceRunPlan plus actual start/finish events to exact report; no count-based pass inference |
| `remote_test_runner_v1` | Dedicated producer calls the existing native test executor and writes the verified report before worker finalization |

Host/private process objects and signing keys never cross the wire. Workers own
their isolated execution data but cannot open the parent's journals or publish
its result/cache index. Parent copies come from the same frozen byte buffers
whose hashes were verified, with readback before publication.

## Cancellation, replay and recovery

All mutations run in one parent command owner. The operation WAL must contain
the exact original envelope in `executing` or `outcome-unknown`; admitted,
cancelled and terminal operations cannot admit a bundle. Cancellation is
restricted to the session's own operation IDs and durably commits before a late
bundle can be accepted.

The task journal append is the completion linearization point. Its stable group
ID is the operation ID, independent of session/window nonce. The operation
terminal commit follows. A restart between these commits reconciles the exact
retained result/process digest without adding another task row; cancellation
after that task append returns `REMOTE_COMPLETION_ALREADY_COMMITTING`.
All remote cancellation must use this serialized adapter, including after
reopen. Bypassing it through a generic operation journal can violate the joint
recovery protocol. The parent publishes no accepted result/cache pointer until
both commits have succeeded. Private staging is keyed by completion digest
within the current window and remains quarantined on failure.

## Provider boundary

The native-domain adapter starts only a local worker on the enrolled host,
using the existing BuildRunner process owner. It requires terminal observation,
exact local tree/capacity closure and pre/post input validation before signing.
The frozen compiler image is pinned by the existing worker. A supplied process
port is protected composition, not worker-controlled data.

Container mode must use the common versioned Simple Container lifecycle API:
Linux selects Podman and Windows selects Docker. Container completion requires
its exact runtime identity, owner cleanup/absence receipt and actual output
capture. The native-domain adapter and existing host create/start observation
do not constitute container completion. No raw engine CLI or SSH-completion
shortcut is introduced by this slice.

## Bounds and qualification

Policy bounds aggregate evidence to at most 256 MiB for typed in-process
collection. The wire bundle has a stricter 4 MiB decoded aggregate, 16 MiB wire,
16 KiB binary chunks and 4096 outputs. Larger outputs fail explicitly.
The protected caller supplies freshly observed current time/authority state.
No hot path scans repository trees or reconstructs operation history.

The source-authored unit/integration specs exercise crypto mutation, outputs,
tests, cancellation, replay and orderly WAL reopen. They are not executed
evidence. Native and container provider qualification, actual process crash
recovery, real remote transport, Windows Docker/Linux Podman smoke, performance,
SPipe docgen and final review remain required before admission.
