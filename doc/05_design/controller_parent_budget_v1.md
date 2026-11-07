# Existing parent aggregate helper budget

## Scope

ControllerParentBudgetV1 binds one existing parent host operation and immutable
assignment to maximum aggregate CPU/memory and a complete ContainerHostScopeV2.
It is not another reservation, ledger, scheduler or host effect. The parent keeps
its existing host operation, identity, resources and recovery obligations.

Public bytes/digest/decode helpers canonically encode version1 SDN with a16KiB
UTF-8 byte ceiling. Scope is the existing canonical V2 scope string; alias,
native machine, service, provider generation and honest continuity mode/ID remain
separate. Scope hash in the retained intent's legacy fence.boot_id slot is an
opaque internal fence, NOT observed native OS boot proof.

controller_parent_budget_match_v1 receives the already retained parent binding
and controller assignment operation from its owner. It checks exact canonical
host-operation ID/digest and assignment digest, controller_assignment_match_v1,
physical alias/service/generation and the all-field internal scope fence hash.
Changing native identity, service incarnation or continuity mode cannot collide
with another parent fence merely because an alias or counter looks similar.

The budget operation action is controller_helper_budget_v1 at the parent
controller ID. Principal/project/environment/policy/revocation/session equal the
parent host operation. Its memory equals maximum aggregate memory and positive
duration cannot exceed the parent duration. Positive aggregate CPU/memory must
be at least the parent's ALREADY retained reservation. This module compares
values without addition or multiplying resource sums, avoiding aggregate overflow.

## Signing and host-owned atomic admission

The generic grant has no CPU field. CPU is explicitly included in canonical
budget bytes; the operation payload_digest binds those bytes, and a real signed
grant/human approval must bind the exact operation before host admission.
ControllerParentBudgetProofV1 carries budget/operation/signed/approval using the
existing canonical codecs. Its outer wire ceiling is256KiB bytes; nested payload
is16KiB. Decode/encode/match establish structure and integrity only, not authority,
key publisher trust, current grant validity or membership in an existing ledger.

Host must independently load the actual retained parent binding/operation,
verify this action's signed grant AND human approval against protected current
snapshots, then atomically charge PARENT PLUS ALL HELPERS in the SAME physical
ledger/capacity authority. Do not charge only helpers, double-charge a second
parent reservation, or accept individually feasible concurrent helpers that
overcommit their aggregate ceiling. Overflow-safe comparisons/delta accounting,
exclusive devices, unknown outcomes, cancellation and provider absence remain
host owner responsibilities. No timeout frees parent or helper capacity.

## Executable scope and qualification

Spec controller_parent_budget_spec.spl and acceptance fixture
orchestrator_acceptance/controller_parent_budget.spl contain eight real typed
binding/wire scenarios: exact parent references; coherent mismatched-parent
rebinding; alias/native/service-mode fences; retained-parent minimum ceilings;
operation metadata/deadline/memory; CPU payload binding; i64/byte bounds; strict
nested proof framing. Proof fixtures use actual Ed25519 signing-message helpers
and real signatures, but DO NOT claim an authority verification PASS. Host-signed
and atomic-ledger consumer acceptance belongs to the host owner.

No production API, owner source, earlier staged controller paths or ledger code
was edited. No builds/tests/manual generation ran. Runtime/admitted/full-system
qualification remains NOT_RUN; this is a necessary helper-budget dependency.
Authored ORCH-02/HOST-02 traceability intent uses the existing pending shorthand
requirement reconciliation, not inferred complete requirement coverage.
