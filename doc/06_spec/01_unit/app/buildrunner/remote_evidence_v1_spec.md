# Remote evidence bytes V1

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler, seed,
test runner, or real remote host was executed for these specifications. This is
an inventory of intended assertions, not generated execution evidence or a
coverage claim.

Source: `test/01_unit/app/buildrunner/remote_evidence_v1_spec.spl`.
Implementation: `src/app/buildrunner/remote_evidence_v1.spl`.

The fixture declares two toolchain inputs, binds their ordered inventory digest
to the task, and pins encoded policy bytes through
`remote-policy/remote_task.sdn`. Process payloads use
`build_runner_process_evidence_encode_v1`; stdout, stderr, program bytes,
reports, and result output claims have computed SHA-256 digests. The encoded
process observation is fixture data and does not claim actual process launch,
tree reap, signed host completion, or scheduler publication authority.

| Scenario | Intended assertion |
| --- | --- |
| Valid build | Frozen output inventory follows declared task order despite reversed download order; process, result, log, inventory, and empty test digests match actual fixture data. Binary bytes include zero and 255. |
| Valid test | Exact ordered task-bound `case_alpha` and `case_beta` passing rows produce the report and test digests. |
| Output substitution | Changing downloaded bytes with original result claims, or changing claims with original bytes, rejects on the parent output digest comparison. |
| Process log substitution | Changing either stdout or stderr without changing the encoded process observation rejects. |
| Stale task | Attempt changes reject old result identity; a freshly bound result with old process identity independently rejects. |
| Policy or toolchain changes | Changed epoch, missing policy pin, changed toolchain inventory digest, absent tool input, and changed tool-input digest reject. |
| Output membership | Duplicate and unknown downloaded output paths reject. |
| Result membership | A different host, duplicate result output claims, and an unknown claimed output reject independently. |
| Missing test report | A result claiming a report whose bytes were omitted rejects through declared-output completeness. |
| Invalid test rows | Missing, zero, skipped, failed, unknown, duplicate, reordered, and aggregate-only rows reject even after recomputing result digests from those report bytes. |
| Copied report | Passing rows bound to a different task attempt reject. |
| Invalid test policy | Empty or duplicate expected inventories and an undeclared report path reject. |
| Total bytes | Exactly sufficient cumulative process/log/output budget accepts; one byte less rejects; a budget covering only process payload rejects when logs are added. Each budget is pinned before fixture identity is created. |

The missing-report scenario intentionally expects the current completeness
error, `success requires every declared output and fresh parent digest`.
The more specific `REMOTE_TEST_REPORT_MISSING` branch follows that check and
cannot currently be reached by a successful result with a declared report.

Execution remains pending runtime qualification. No PASS status is asserted.
