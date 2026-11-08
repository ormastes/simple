# Remote exact-case test report bridge V1

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler, seed,
test suite, report-producing runner or real remote process ran for this evidence.

Source: `test/01_unit/app/buildrunner/remote_test_report_v1_spec.spl`.
Implementation: `src/app/buildrunner/remote_test_report_v1.spl`.

`remote_test_report_from_events_v1(task, policy, plan, actual_files)` accepts a
test policy already pinned through the ordinary remote policy binding. It
encodes the `TraceRunPlan` canonically and requires its SHA-256 in the task input
`remote-tests/<task.id>.sdn`. The plan run ID must equal the policy operation ID;
its binary, subject and configuration IDs must equal the task producer, source
and toolchain digests. Its ordered case IDs must equal `policy.expected_tests`.
The expectation ID remains opaque but its exact bytes are covered by the plan
input hash. No unpinned expectation is inferred.

The bridge reuses `reconcile_trace_case_events` to match source-file paths and
case names against the independently pinned plan. Every expected case must have
one start and one terminal passed event. Missing, interrupted, duplicate,
unknown, failed, pending or skipped observations cannot produce a report.
Only after reconciliation does the bridge construct
`SIMPLE-REMOTE-TEST-REPORT-1`, the final task identity and one ordered
`<case_id>\tpassed` row per expected case. The existing remote report validator
checks the produced format.

The pure document entrypoint
`remote_test_report_from_documents_v1(task, policy, plan_source, documents)`
requires canonical plan source bytes, decodes real SDN case-event arrays with
the shared decoder, and delegates to the same bridge. Its aggregate source/path
budget is 4 MiB and its file limit is 4,096. Neither entrypoint reads files,
writes a report or runs a process.

| Scenario | Intended assertion |
| --- | --- |
| Completed observations | Two synthetic started/finished-passed pairs produce the exact task-bound report in pinned policy order even when emitting files arrive in reverse order; the existing report validator accepts its digest. |
| Missing observations | Empty files, absent cases, started-only cases and terminal events without starts reject. |
| Duplicates | Duplicate starts, terminal events and emitting file paths reject. |
| Identity mismatch | Unknown case names and another emitting source path reject. |
| Nonpassing observations | Failed, pending and skipped cases produce no passing report. |
| Plan binding | Changed operation, binary, source or toolchain identity rejects. |
| Canonical hash | Changed opaque expectation ID, changed pinned input hash and missing plan input reject. |
| Ordered inventory | Reordered or missing planned case IDs reject before event interpretation. |
| Policy binding | Build action and a policy changed after its task hash was pinned reject. |
| Document bridge | Canonical plan and encoded SDN events produce the same report; alternate plan formatting and truncated event SDN reject. |

Integration contract: the selected test-runner producer must collect its actual
framework events, call this bridge and write the declared report path before it
returns and the generic worker finalizes task outputs. The generic worker
cannot retrofit a missing report after it has already reported an output error.
This pure bridge is available for that runner; the unit fixtures do not claim
that a production runner has invoked it or written any report.

Framework events and a generated report are observations, not independent proof
that tests ran. Host process ownership/tree retirement, digest-pinned producer
execution, exact result/output bytes, signed completion, current authority and
parent replay/fencing checks remain separate mandatory gates. Runtime execution,
coverage and end-to-end report production remain unverified.
