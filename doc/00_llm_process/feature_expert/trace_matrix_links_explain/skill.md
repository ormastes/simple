# Feature expert: trace matrix, links, explain, diff, report

Plan: `simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md` section 6 (6.1 CLI, 6.2 matrix, 6.4 profiles).
Sibling slice: `doc/00_llm_process/feature_expert/trace_command_family/skill.md` (profile + `trace missing`).

## Where things live
| Concern | File |
| --- | --- |
| Shared per-requirement status, `TraceCommandVerdictV1`, evidence type | `src/lib/common/traceability/query_status_v1.spl` |
| `trace matrix` (feature/component/layer axes) | `src/lib/common/traceability/query_matrix_v1.spl` |
| `trace links --check` (dangling and mis-kinded edges) | `src/lib/common/traceability/query_links_v1.spl` |
| `trace explain <id> --why-incomplete` | `src/lib/common/traceability/query_explain_v1.spl` |
| `trace diff --base --head` | `src/lib/common/traceability/query_diff_v1.spl` |
| `trace report` | `src/lib/common/traceability/query_report_v1.spl` |
| Options / render / runner | `src/app/traceability/query_cmds_{options,render,main}_v1.spl` |
| Dispatch (2 lines + 1 import pair) | `src/app/traceability/query_main.spl` |

## Contracts to keep
- Each subcommand is one pure module (graph in, value out) plus a pure text/SDN renderer; the app layer only parses, loads the snapshot, calls, prints.
- A structural link is `Linked`; `Verified` needs a `TracePassingEvidenceV1` naming a requirement that already has a verifying link. Evidence for an unlinked requirement verifies nothing.
- Exit codes: 2 when the graph is incomplete or the profile is not `worktree` (wins over everything), 1 for a `links` issue or an unknown `explain` id, else 0. Absent links in an incomplete graph are `Unknown`, never `Missing`.
- Shared snapshot options (`--snapshot --format --limit --spec-root --bug-db --path --declaration`) are validated by feeding them to the `missing` parser, so there is one validator.
- Matrix: requirements with no entity on an axis are `unassigned`, not silently dropped; empty cells are omitted from `cells`, never shown as green.

## Verify
`bin/simple test test/01_unit/app/traceability/trace_matrix_spec.spl test/01_unit/app/traceability/trace_links_explain_diff_report_spec.spl test/01_unit/app/traceability/trace_cmds_options_spec.spl`

Open work: `doc/08_tracking/bug/trace_cmds_no_passing_evidence_source_2026-11-15.md`.
