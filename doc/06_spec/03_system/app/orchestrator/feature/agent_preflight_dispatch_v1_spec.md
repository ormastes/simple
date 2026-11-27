# Expected AgentSession preflight dispatch packet

Status: **NOT_RUN**. Authored manual; no generated or runtime PASS evidence.
Requirements: ORCH-02 immutable association; HOST-02 exact scoped dispatch input.
Spec: `test/03_system/app/orchestrator/feature/agent_preflight_dispatch_v1_spec.spl`.

Setup: import actual common codecs and existing real signed V2 dispatch fixtures.
Wrap each platform packet with an expected binding for a separate AgentSession UID.
The outer frames deliberately reuse a real assignment signature for codec shape;
that signature does NOT authorize the new preflight action. No authorization
success, native probe, observed capability or fake provider is claimed.

| Exact step | Procedure / checks |
|---|---|
| round trips both backend packets while preserving all four original proof pairs | Round-trip Linux and Windows wrappers. Compare full nested dispatch bytes to preserve all four original proof pairs, and compare outer frames separately. |
| derives separate expected association authorization while preserving scoped envelope fields | Derive new action/id/payload and compare full canonical operation with an expected copy preserving every other original scoped field. |
| refuses controller host identity and exact nested plan mismatches | Refuse mismatched controller, inherited host identity, request digest and native machine in the exact nested plan. |
| changes authorization payload for expected image and task without changing dispatch proofs | Change expected image/task; payload changes while stable ID and all inner dispatch proofs remain unchanged. New action proof must be verified separately by owner. |
| refuses strict outer shape canonical and byte boundary violations | Refuse wrong version type/kind, unknown observed claim, typed binding, missing proof, extra newline, duplicate version and 4194306-byte UTF-8 source. |

Encoding hashes/serializes exact expected values, not actual observations. The
canonical outer limit is 4 MiB in bytes; nested dispatch and binding retain their
own tighter limits. Escaping overhead may reject a nested-valid combination;
bytes are never truncated. Actual service-owned authorization verifies the new
expected task/image/probe association proof and all four existing dispatch proofs,
then performs semantic platform validation and normal journal/host admission.
This pure contract does not implement those effectful gates. Builds and test runs
were prohibited for this task.
