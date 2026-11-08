# Host runtime exec original intent and packet integrity

Status: **NOT_RUN**. Authored manual; no generated/native/runtime PASS evidence.
Requirements: ORCH-02 exact original parent association; HOST-02 action/hash domains.
Spec: `test/03_system/app/orchestrator/feature/host_runtime_exec_v3_spec.spl`.

Setup: use actual neutral exec/intent codecs and the existing real V2 assignment,
parent host/controller envelopes and signed-frame fixture. Hash exact retained
parent reference and both envelopes; bind their original workload/plan/scope into
the exec request. Outer proof frames are deliberately reused for SHAPE only and
do not authorize this new intent/action. No positive signature verification,
native exec, provider response or host historical assignment storage is claimed.

| Exact step | Procedure / checks |
|---|---|
| round trips intent packet and exact proof frames without claiming signature authority | Round-trip canonical intent/packet and preserve exact existing proof frame bytes and packet digest. |
| binds each original parent and control digest into the signed intent domain | Change host envelope, assignment, controller envelope, parent provider, exec-control digest or request nonce; each changes intent hash. |
| refuses raw exec digest as operation payload and wrong child action or physical alias | Accept intent-hashed operation shape; refuse raw exec request hash, parent operation ID, wrong action and native-machine-as-authorized-alias. |
| requires original assignment host envelope controller envelope and exact retained parent plan | Rebind child payload after tampering each parent digest, retained parent plan, or controller envelope; packet still refuses the inconsistent original chain. |
| requires admission flat fields to match original intent and keeps deadline in raw request domain | Flat admission fields must equal original intent. Parent baseline cannot replace exec-control pin; deadline must use raw request hash, not intent hash. |
| refuses unknown duplicate mistyped missing and noncanonical intent or packet fields | Refuse unknown, wrong-type, duplicate, missing, wrong-kind and noncanonical intent/packet fields. |
| refuses malformed digest and nested request sizes at exact byte bounded domains | Refuse malformed control digest, intent over2MiB, packet over4MiB and nested exec request over1MiB using byte counts. |

HostRuntimeExecIntentV3 includes raw64 original host operation digest, assignment
reference digest, original controller operation digest, parent provider baseline
and exec-control owner identity. Packet stores parentBinding as existing canonical
reference bytes, parentIntent and parentHostOperation originals, and the original
parentControllerOperation. Existing assignment restore/match helpers verify the
chain; no duplicate assignment grammar or guessed reservation attempt is added.
The parent plan hash binds attempt; assignment_generation retains its distinct role.

The operation payload is SHA256 of canonical INTENT, never raw exec request. The
effect deadline deliberately remains raw exec request digest/op/exec-only action.
Admission carries original intent; its flat request/parent/control fields must
agree. Host independently resolves retained parent/provider/control owners and
verifies current action-specific signatures, journal begin and exclusive broker
claim. Decoding provides none of that authority and asserts no historical host
assignment record. Bounds are1MiB nested request/2MiB intent/4MiB packet via str_len;
escaping overhead may reject nested-valid combinations rather than truncate.
Timeout still bounds provider control/observation calls only; running/unknown
work remains owned and charged. Builds/tests were prohibited for this task.
