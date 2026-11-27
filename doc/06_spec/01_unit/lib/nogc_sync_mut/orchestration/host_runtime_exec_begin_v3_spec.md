# Signed exec child begin specification

Executable: `test/01_unit/lib/nogc_sync_mut/orchestration/host_runtime_exec_begin_v3_spec.spl`.
Requirements: HOST-02, ORCH-02. Status: **NOT_RUN**, authored manual.

| Scenario | Observable assertion |
|---|---|
| Wire bounds/syntax | Malformed and oversized packets return no lease, preserve actual WAL sequence and consume no scripted provider result |
| Signature before native read | Canonical packet with a corrupt approval returns APPROVAL_SIGNATURE_INVALID before resolver progress |
| Expired child | Exact approval expiry rejects without inspecting or releasing the charged parent |
| Quarantine | Unproven current continuity rejects before native reads |
| Existing child | Executing, outcome-unknown, completed, failed and cancelled actual WAL rows never mint a lease or invoke the resolver again |
| Admitted retry | An admitted row missing its mandatory original private archive rejects before native reads |
| Expired durable BEGIN | Actual private archive and WAL BEGIN precede two calls at approval expiry; both preserve executing owner/sequence/parent charge and mint no lease |
| Prior delegation | Even a synthetic orphan final prevents first-begin from decoding/minting authority |
| Resolver failure | An explicit failed scripted native read returns the advanced Container owner and no lease |
| Resolver success/refusal | Successful scripted resolver progress followed by absent protected installation returns the advanced owner, unchanged child journal and no lease |
| Architecture recurrence | Only completed installation loader and shared publisher feed the lease; recorded begin sequence/revision are used; no direct leaf provider, native creation, admission decoder or release route |

Fixtures use the actual signed executor, real owned operation journal, production
enrollment-derived capacity authority and private policy file. Provider commands
and root/native facts remain explicitly synthetic. The signer is independently
checked through the real SDK verifier; no trusted native readiness is inferred.
Owned close uses its canonical cleanup turn rather than legacy boolean close.

None of these eleven scenarios is executed. The expired durable-BEGIN replay
case does not exercise an in-call clock transition after native probe/BEGIN.
No positive native probe/first lease,
fault-injected final publication, retained native control cleanup, helper stream,
broker one-use claim or gateway priority responsiveness is qualified. Those
acceptance cases require actual configured native evidence. No build, seed or
test campaign was started. Existing unknown/terminal refusal is not completion
of resume-start authorization or the complete native exec lifecycle.
