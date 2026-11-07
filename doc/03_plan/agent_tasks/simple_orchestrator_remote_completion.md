# Remote completion implementation ownership

Requirements: RUN-01, RUN-02. Status: AWAITING_VERIFICATION.

| Lane | Owner | Review |
| --- | --- | --- |
| Completion signature/codec, binary bundle transport, exact-case reporter, policy codec | Sol sidecar `completion_authority` | Astra remote-runner lead |
| Evidence mutation and parent cancellation/replay/WAL specs | Sol sidecar `evidence_specs` | Astra remote-runner lead |
| Policy, host execution, parent publication, test producer, documentation | Astra remote-runner lead | Root Astra integration review |
| Common Container lifecycle/cleanup API | Orchestrator/platform leads | Their owning leads plus root integration |
| Isolated source integration and PR merge | Root task owner | Root task owner |

The shared interfaces were fixed before sidecar edits. Sidecars wrote real
assertions and source-authored manuals and explicitly reported no runtime test
execution. Source review found and corrected the host public-key tuple field,
foreign-operation cancellation and cancellation between durable commits. Final
admission still requires an executable/runtime review; lower-model source review
does not establish generated-manual quality, coverage or qualification.

The compiler/bootstrap six-cycle stop condition remains in force. No compiler,
seed, SPipe/docgen or native test retry is authorized in this slice. Root retains
the complete feature goal and future native/container qualification obligations.
