# trace matrix/links/explain/diff/report: no passing-evidence source wired to the CLI

Status: open. Found 2026-11-15 while adding the commands.

`src/app/traceability/query_cmds_main_v1.spl` (the `val evidence` line in `run_trace_cmd_v1`) always passes an empty
`[TracePassingEvidenceV1]`, so from the CLI no requirement can reach `Verified`; everything structurally linked is
`Linked`. The pure modules already promote to `Verified` when evidence is supplied (specs prove it).

Unblock: a read-only projection from the RunnerTestDb (plan section 3.5) of passing cases to requirement ids,
keyed to the same snapshot. Not wired here because no snapshot-bound run source exists in `TraceSnapshotBuild`.

Also not done: `matrix --filter`, `--format=md|html` for `report`, `links --scope=doc` Markdown/SDN link lint
(plan 6.3, `src/app/doc/semantic_link_lint.spl`); `links --check` verifies graph edges only.
