# Remote completion implementation ownership

Requirements: RUN-01, RUN-02. Status: AWAITING_VERIFICATION.

| Lane | Owner | Review |
| --- | --- | --- |
| Completion signature/codec, binary bundle transport, exact-case reporter, policy codec | Sol sidecar `completion_authority` | Astra remote-runner lead |
| Evidence mutation and parent cancellation/replay/WAL specs | Sol sidecar `evidence_specs` | Astra remote-runner lead |
| Policy, host execution, parent publication, test producer, documentation | Astra remote-runner lead | Root Astra integration review |
| Common Container lifecycle/cleanup API | Orchestrator/platform leads | Their owning leads plus root integration |
| Isolated source integration and PR merge | Root task owner | Root task owner |
| Typed container/native journal union, mixed replay/snapshot specs, nonce probe, bounded producer argument specs | Sol sidecar `completion_authority` | Astra remote-runner lead and root exact-head review |
| Container signature/wire codecs, signed parent integration, staging mutation specs and paired manuals | Sol sidecar `evidence_specs` | Astra remote-runner lead and root exact-head review |
| Container host lifecycle, measured user/probe evidence, dedicated producer and parent acceptance | Astra remote-runner lead | Independent Astra review plus root integration |

The shared interfaces were fixed before sidecar edits. Sidecars wrote real
assertions and source-authored manuals and explicitly reported no runtime test
execution. Source review found and corrected the host public-key tuple field,
foreign-operation cancellation and cancellation between durable commits. Final
admission still requires an executable/runtime review; lower-model source review
does not establish generated-manual quality, coverage or qualification.

The compiler/bootstrap six-cycle stop condition remains in force. No compiler,
seed, SPipe/docgen or native test retry is authorized in this slice. Root retains
the complete feature goal and future native/container qualification obligations.

The native source checkpoint was merged separately. Container V2 extends the
same task WAL and shared Container API; no native checkpoint commits are to be
re-landed. Provider owners supply actual Linux Podman / Windows Docker effects,
bounded complete logs, selected-user observation, exact absence and protected
workspace execution capability. The buildrunner never supplies app-local engine
commands, synthetic PID evidence, recursive chmod or inferred Windows SID/ACL
authority. Remaining source integration and runtime qualification are explicit
dependencies, not reasons to label RUN-01/RUN-02 complete.

## Unavailable host and capability rows: open Todo DB rows and resume plans (2026-11-19)

SPipe completion rule: a row whose host or capability is unavailable is BLOCKED with an open Todo DB row and a resume
plan. It is never skipped and never counted as done. Nothing below is PASS; every spec is NOT_RUN. Records live under
the untracked `.spipe/simple_orchestrator/continuation_20261116/` (handoff `progress_handoff_0010.md`, audit
`container_gap_audit_20261116.md`, milestone dirs). Credentials, server addresses, accounts and fingerprints are never
written to tracked files; they go only to untracked records.

| Todo row | Row | Owner | Missing prerequisite | Resume command | Retained artifacts |
| --- | --- | --- | --- | --- | --- |
| 455 | Spec execution NOT_RUN | boot-fable bootstrap lane, then SIMPLEORCH lane | No full-CLI pure-Simple binary on this host; wait for boot-fable Stage 4 | After Stage 4 lands: `bin/simple test <spec> --no-session-daemon` per spec, first the queue PRs #9670 #9671 #9673 #9674, then every orchestrator spec those and later PRs touched (list in the handoff and skill.md) | handoff, milestone receipts |
| 193-195 | Container live rows ENV-BLOCKED | SIMPLEORCH lane | docker socket permission denied; AppArmor `apparmor_restrict_unprivileged_userns=1` blocks rootless runc | see `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md`; then `bin/simple test test/02_integration/app/ci/pipeline_runner_spec.spl --no-session-daemon` | `container_gap_audit_20261116.md` (16 rows) |
| 456 | Windows, FreeBSD, VM host rows | SIMPLEORCH lane with platform leads | No Windows host, FreeBSD host or VM host; related container rows 365 373 374 | Per host, once provided: run the audit rows for that host through the shared lifecycle specs with receipts | container gap audit |
| 457 | Live remote enrollment | owner (user) then SIMPLEORCH lane | Owner-provided server, SSH account and expected host fingerprint | Run the remote enrollment acceptance flow with the values supplied through an untracked record | untracked enrollment record, receipts |
| 458 | Operator key-policy enrollment; Linux controller root provisioning | operator (owner) | Operator enrolls kinds `host_execute_associated_v3`, `host_agent_cancel_v4`, `helper-abandon`, `service-handoff-abandon`, `remote-run-abandon`, `retention-release` in the key policy; Linux controller root provisioned out of band | After enrollment: rerun the controller and host acceptance specs that sign with each kind | key-policy records (untracked) |
| 459 | Agent workspace close | owner | Deferred by owner on 2026-11-19 | Reopen the agent workspace close lane on owner go; first verify the landed workspace v2 specs | milestone records |
