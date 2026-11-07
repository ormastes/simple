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
| `remote_container_authority_v2` | Separate container completion signature domain, original scoped grant/approval and enrolled host verification |
| `remote_container_evidence_v2` | Pinned common container request/provider, actual wait/absence evidence and transferred output bytes |
| `remote_container_host_v2` | Shared Container API lifecycle, retained actual wait before destruction, exact independent absence and host signing |
| `remote_container_session_v2` | Container parent admission using the existing operation and task journals |
| `remote_container_stage_v2` | Bounded immutable byte staging with exclusive claims and absent output leaves |
| `remote_container_producer_v2` | Dedicated in-container build/test entrypoint; nonce access preflight precedes every action |
| `remote_container_workspace_probe_v2` | Actual same-process exclusive write/read/delete cycle, bound to task identity and fresh host nonce |
| `task_runner.execution_identity_v2` | Tagged native/container attempts; native encoding remains unchanged and container records contain no invented PID |

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

The V2 producer consumes the common owner, exact action/mount projection, actual
wait and logs, then destroys the exact object and requests a positive absence
observation. It retains the original wait across destruction. Its effect
deadline is derived from the original grant/approval expiry; cleanup remains
available after expiry. The signature binds the canonical common execution
evidence, all output bytes and the exact test report. The parent recomputes
these bindings before publication. Native V1 admission remains native-process
only; container V2 cannot be downgraded into a native process record.

V2 extends the existing task journal table and WAL replay with a tagged record;
it does not create a second journal. Native public readers reject container
records rather than losing their execution identity. Mixed history and snapshot
readers preserve both variants. Container projection rows are bounded before
the WAL commit so filtered snapshot groups remain decodable.

Workspace byte staging does not establish executable permissions. Those require
the shared provider's protected workspace capability. The portable stager
neither changes ACLs nor invokes engine or platform commands. Before task
approval it reserves a cryptographically random nonce under an exclusive host
claim. The approved task pins the nonce input and declares the probe output.
After create and before start the host obtains the exact engine-selected-user
receipt. The dedicated producer then performs the actual same-process access
cycle before invoking build or tests. The completion signature binds both
receipts, and the parent checks the nonce and exact successful output bytes.
The engine receipt identifies the configured selected user; it does not claim
to observe an effective OS UID or Windows SID. Least-privilege token/ACL
behavior requires real platform qualification. Provider capture must reject
truncated logs before the completion signer can accept them.

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
