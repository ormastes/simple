# Actual expected-preflight action authorization

Status: **NOT_RUN**. Authored manual; no generated/runtime PASS evidence.
Requirements: ORCH-02 action-specific immutable authorization; HOST-02 refusal before effects.
Spec: `test/03_system/app/orchestrator/feature/agent_preflight_authority_v1_spec.spl`.

Setup: reuse the actual V2 signed dispatch/snapshot fixture, derive the new expected
association authorization operation and sign it with real Ed25519 issuer seed1
and distinct approver seed65. Use SDK grant/approval signature-message and grant
hash functions; add the new action to both scoped controller keys. Synthetic
clock100 is only an internal SDK test boundary; actual command uses its native
clock/private context. No provider or engine result is simulated.

| Exact step | Procedure / checks |
|---|---|
| verifies separately signed new action using actual SDK issuer and human approval | Actual controller_preflight_authorize_v1 must return the new grant; both real signatures are 64 bytes and action is exact. |
| refuses assignment action replay and each independently forged proof | Replay original assignment grant/approval and refuse; independently forge issuer and approver signatures and refuse each. |
| refuses changed expected image or task under otherwise valid signed action | Change expected image then task digest with original valid proofs; refuse both changed operation digests. |
| denies expired revoked and incorrectly scoped authority contexts | Refuse expired approval, revoked scoped issuer, wrong controller/epoch and nonpositive clock. |
| refuses malformed packets and extra public command arguments without acquiring a journal | Write malformed packet to own secure temp root, invoke actual public command for dispatch/resume and extra arguments, and refuse extra inspect args. Assert no journal directory appeared; remove own files. |

Successful SDK verification authorizes the expected immutable association only;
it does not establish installed CLI/version/capability, selected effective user,
actual image-probe output or execution completion. Inner four action proofs,
semantic platform validation, retained desired/policy matching, charged child
admission and immediately-before-execute checks remain actual owner obligations.
These tests do not claim their composed engine/platform path ran. Builds/test
execution were prohibited for this task.
