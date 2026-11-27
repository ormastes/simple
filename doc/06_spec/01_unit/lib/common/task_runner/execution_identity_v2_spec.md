# Typed task attempt execution identity V2

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler, seed,
unit suite, native process, container or durable journal was executed.

Source: `test/01_unit/lib/common/task_runner/execution_identity_v2_spec.spl`.
Implementation: `src/lib/common/task_runner/execution_identity_v2.spl`.

`TaskRunnerAttemptRecordV2` is an explicit `Native(TaskRunnerAttemptV1)` or
`Container(TaskRunnerContainerAttemptV2)` union. Common getters project only
task identity, group, attempt, status and result digest. A native record encodes
through the unchanged V1 codec and retains its mandatory positive PID, positive
process generation, actual tree retirement and typed native crash requirements.
Its wire bytes remain exactly V1. A container record carries the common
`ContainerExecutionEvidenceV2` value directly, including execution plan, runtime
identity, provider identity, exit observation, wait digest and exact absence
receipt. It has no fake PID, process generation, signal or reap boolean.

Container records use `SIMPLE-TASK-CONTAINER-ATTEMPT-2` framing, existing storage
escaping, common evidence canonical encoding and a 65,536-byte record bound.
Each new container record's outer escaped projection bytes plus a conservative
32-byte sequence/tab/newline allowance must also fit 16,320 bytes. This cap is
container-only: historical native V1 encoding/admission is unchanged. It keeps
eight container rows replayable even when a snapshot filters an older group
whose records never coexisted in the global newest-eight projection.
Container attempt number must match the common execution plan. Passing requires
zero common exit, zero task exit, empty reason, validated result and its digest.
Ordinary failure requires nonzero exits, a validated result/digest and an
attributable compile/assertion reason. Abort currently permits infrastructure
only and cannot claim a validated task result. The common evidence has no typed
crash, timeout or cancellation cause: container `crashed` and those inferred
abort reasons are rejected. Exit 139 or 137 never becomes signal proof.

| Scenario | Intended assertion |
| --- | --- |
| Native compatibility | Native V1 encoded bytes remain identical; all getters and decoded positive process identity/reap values survive. |
| Native invariants | Zero PID, zero generation and unreaped tree reject. |
| Typed native crash | Confirmed signal evidence survives; removing the signal while retaining a crash exit rejects. |
| Framing | Unknown version, truncated native input and input above the wire bound reject. |
| Container roundtrip | Canonical common execution evidence, exact native container identity and absence proof remain a Container variant; all getters and wire bytes survive. |
| Passing constraints | Nonzero outer/task exit, unvalidated result, missing result digest and a passing reason reject. |
| Failure constraints | Validated compile/assertion failures with genuine nonzero synthetic exits encode; zero exit substitution, unsupported reason and unvalidated result reject. |
| Conservative causes | Container exit 139 cannot establish a crash; infrastructure abort without validated result is representable; unproved timeout/cancellation abort reasons reject. |
| Common identity integrity | Different record attempt, absence proof kind and native runtime identity reject. Trailing rows, noncanonical decimal and nonboolean validation flag reject. |

The shared fixture uses the actual common `container_execution_evidence_v2`
constructor, `container_scope_fence_id_v2`, and canonical runtime query/observation
digest helpers. Provider wait and absence observations are synthetic values;
they demonstrate structural codec contracts without claiming those queries ran.
No substitute receipt type or guessed absence-digest formula is used.

Canonical decoding is structural integrity, not signed authority or permission
to append. Actual issuer/approver/host signatures, current fences, result-byte
acceptance and durable replay consumption remain parent-owned. Native-only
history APIs must report an error when encountering a container, preserving the
union instead of downgrading it to a made-up native process.

Execution and coverage remain unverified. No PASS is asserted.
