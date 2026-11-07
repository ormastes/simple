# Aggregate parent/helper budget binding

Status: **NOT_RUN — awaiting verification**. Authored manual, not generated
execution evidence or a signed-authority/ledger PASS.

Spec: `test/03_system/app/orchestrator/feature/controller_parent_budget_spec.spl`.
Fixture: `test/fixtures/orchestrator_acceptance/controller_parent_budget.spl`.
Contract: `src/lib/common/contracts/orchestration/controller_parent_budget_v1.spl`.
Authored labels ORCH-02/HOST-02 are assertion intent pending existing requirement
reconciliation; no complete NFR or coverage qualification is claimed.

## Setup

Construct an actual canonical parent reservation intent and host operation,
immutable controller assignment and matching controller operation. Its full scope
uses a distinct physical alias and colon-prefixed native machine/service identity,
EMPTY native boot and an explicit service incarnation. The retained legacy
intent fence is the common all-field scope hash, not a fabricated OS boot.

The retained parent charge is CPU2000/memory4000; the aggregate ceiling is
CPU6000/memory12000. Budget operation memory equals12000 and duration100 stays
within parent duration200. Proof-frame fixtures use real deterministic Ed25519
signing helpers over the existing grant/operation codecs. There is no protected
publisher registry or SDK authorization invocation in this pure structural suite.

## Scenarios and exact checks

| Scenario | Steps and required observations |
|---|---|
| Exact retained parent | Match operation ID and canonical operation/assignment hashes. Roundtrip budget and proof, verify exact canonical bytes/digest and retained aggregate values/scope. |
| Rebound wrong parent | Change parent ID, host-operation digest or assignment digest, then coherently recompute budget operation payload; each still fails parent-reference match. Reject altered controller assignment envelope. |
| Full scope and mode separation | Coherently rebind a different alias, native machine, owner incarnation or native-mode scope; reject retained-parent fence mismatch. Equal-looking service/native IDs still have different all-field scope hashes. |
| Aggregate minimum | Refuse CPU1999 or memory3999 after coherent operation rebinding because those are below retained parent charges. Refuse zero/negative maxima. |
| Controller budget envelope | Refuse wrong controller host/action/memory, nonpositive or excessive duration, principal/project/environment/policy/revocation/session mismatches. |
| CPU explicitly signed in payload | Change CPU without changing payload hash and refuse. Rebind and actually re-sign a permitted changed CPU ceiling: payload and approval signature change and canonical framing is preserved. This is not host admission. |
| Payload bounds | Refuse unknown/duplicate/wrong-type/noncanonical records and numeric i64 overflow. Roundtrip exact i64 maxima as data without summing them. Reject16386 UTF-8 bytes against16KiB payload ceiling. |
| Proof bounds | Refuse unknown fields, altered/noncanonical nested budget, corrupted operation/approval frame, oversized nested payload, outer262146-byte source and noncanonical trailing data. |

Byte cases use the two-byte character é, so scalar count cannot accidentally
replace byte count. The generic V2 operation codec can reject maxima outside its
own wire bounds even when an i64 payload is valid; a data roundtrip is no promise
that such an operation can be signed/admitted under current grant limits.

## Assertion mapping and mandatory host gate

ORCH-02 maps to exact existing parent and controller envelope binding. HOST-02
maps to complete physical authority scope and aggregate ceiling integrity.
Neither matcher nor proof decoding authenticates the caller or reserves capacity.
The parent binding arguments must come from protected retained owner state.

Host must verify the budget action's real signed grant AND human approval, then
atomically account parent plus every helper in the SAME physical ledger. CPU is
inside the signed operation payload although the generic grant has no CPU field.
Host integration must reject aggregate overcommit, sum/delta overflow, invalid
proofs, stale parent generations and unknown-outcome capacity release. This suite
creates no second ledger/reservation, helper process or provider effect and cannot
qualify those host checks. No native build, admitted SSpec, SPipe maintenance,
coverage, provider run or full-system acceptance occurred.
