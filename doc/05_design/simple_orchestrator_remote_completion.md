# RUN-01 / RUN-02 remote completion detail design

Status: **AWAITING_VERIFICATION**. This design describes source behavior, not
executed native or container qualification.

`RemoteEvidencePolicyV1` is an immutable task input. The parent and signer both
recompute its canonical bytes and require the matching declared input digest.
The ordinary BuildTask identity consequently binds policy, assignment, attempt,
action, source, producer, toolchain and all input/output names. Every toolchain
inventory entry must also occur in task inputs with its exact digest.

`RemoteAuthorityContextV1` belongs to protected composition. Its key objects,
clock, observed environment, active fence and policy/session revisions are not
wire inputs. Context admission authenticates the original grant and approval,
matches the exact task payload and checks requested resources/environment. The
completion verifier repeats original authorization and verifies an independently
scoped `execution-host` signature over the measured completion.

The bundle codec transports the result, completion, compiler process payload,
stdout/stderr bytes and output bytes. It applies fixed field/count/byte bounds,
strict lowercase hex chunking and canonical text conversion. No decode result
is a capability. The parent freezes content and verifies exact output inventory,
hashes and test reports before signature admission or journal mutation.

The dedicated `remote_test_runner_v1` entrypoint runs within the existing owned
attempt workspace. It reads the exact task, policy and pinned TraceRunPlan,
rejects selector differences, resolves a declared compiler image and invokes the
existing native file executor. It refuses cached/unverified/skipped/pending
results and reconciles actual per-case start/finish events. It emits the report
before returning to the generic worker, which then hashes declared outputs.
Missing test events cannot become aggregate passes. This producer still requires
an admitted compiled artifact and qualified underlying test/process provider.

Parent acceptance first checks the operation's exact durable envelope and live
state. It creates private, completion-digest-keyed output staging from the frozen
buffers and hashes the resulting files. The task journal then records the
existing typed process/result evidence using operation ID as stable group; the
operation journal records the completion digest and terminal state afterward.
Only success from both owners returns `RemoteAcceptedResultV1`. Error paths do
not return an accepted pointer; their private staging remains quarantined.

Replay is checked through both current operation state and retained task
history. If a task append survived but the operation terminal commit did not,
the exact original result/process evidence is required to finish publication.
Cancellation after that linearization point refuses and requests reconciliation.
All cancellation and acceptance commands are serialized by the same protected
parent owner, including after reopen. A generic direct mutation of its injected
operation journal is outside this protocol.

The legacy `BuildRunnerDatabaseSessionV1.record` and session-open remote guards
remain unchanged. The new session is an explicit API. Native host execution is
separate from container execution. Container work requires the common Simple
Container API, Linux Podman/Windows Docker selection, exact runtime identity and
independent cleanup/absence evidence; native reap files cannot substitute.

The explicit `RemoteContainerDatabaseSessionV2` wraps the same parent session.
Its inventory pins canonical common requests at `remote-container/<id>.sdn`
and the provider identity digest plus newline at
`remote-container-provider/<id>.sdn`. V2 bundles carry common container
execution evidence instead of `compiler.process`; the completion's distinct
signature domain binds that evidence, result, logs, outputs and tests. The
receiver verifies actual bytes and current enrollment before appending a
`TaskRunnerAttemptRecordV2.Container` to the existing task WAL. It rejects a
completion timestamp preceding the actual absence observation. Cancellation
and recovery keep the existing task-append linearization point.

The shared API host adapter checks exact argv, working directory and the one
writable attempt-root mount. It uses prepare/create/start, actual wait and logs,
destroy, and positive exact-native-object absence. The wait observation is
retained before destruction. An original-grant deadline governs create/start;
the original protected authority is rechecked after collection and before
signing. Nonzero exit is not reinterpreted as a process crash or signal.

Container records have bounded canonical framing. The common task index
prepares the new projection before committing WAL, and mixed replay/snapshots
preserve the execution variant. Legacy V1 readers refuse a container history.
Neither a native PID nor a native tree-reaped flag is synthesized.

Container source specs include actual-file staging, separately signed parent
admission, binary mutation under an unchanged signature, cancellation/replay,
mixed WAL reopen and snapshot retention. Platform workspace preparation,
selected-user access preflight and full bounded log capture are provider
integration prerequisites; source implementation alone is not qualification.

The container producer uses a fresh host-generated 32-byte nonce, pinned as
`remote-workspace/<id>.nonce`, and declares
`remote-workspace/<id>.probe.sdn` in the immutable output contract. It exclusively
creates, reads, compares and removes its nonce-named probe twice, then
exclusively writes the task-bound receipt before the action. The host queries
the exact engine-selected user after create and before start, retains that
canonical receipt, and binds it together with the actual workspace receipt and
execution evidence in the V2 measurements digest. Failed build/test completion
retains the probe evidence separately while normal failed outputs remain empty.
No pre-created receipt, stale nonce or changed success output is admitted.

Build invocation uses only the pinned `tools/simple` inside the container,
inherited container stdio and a bounded native-build argument surface with
explicit relative source roots, entry, output, backend and entry closure. Test
invocation reuses the exact-case native producer. The wrapper has no engine or
host execution fallback. Executable workspace preparation remains a shared
provider responsibility; no app-local chmod or ACL command is introduced.

Verification inventory lives in the paired `remote_*_v1_spec.spl` unit and WAL
integration specs. Current evidence is source review only. Real native/remote
execution, container cleanup, real crash recovery, latency/RSS, source-generated
manual review and repository verification must pass before runtime admission.
