# trace command family: remaining plan items after profile + missing (2026-11-14)

Landed: `--profile`, `TraceProfile`, exit 2 for unavailable profiles, `trace missing requirements`
(files in `doc/00_llm_process/feature_expert/trace_command_family/skill.md`).

## Not done (plan section 6)
| Item | Where it goes | Unblock condition |
| --- | --- | --- |
| `trace matrix`, `links --check`, `explain`, `diff`, `report` | new `src/app/traceability/query_*_v1.spl` + `query_options_v1.spl:~35` operation list | needs the MDSOC layer/feature dimensions on graph nodes; none exist in `model.spl` |
| `--reverse`, `--depth`, `--around` on `show` | `query_options_v1.spl` option switch (~line 80) | multi-hop traversal over `TraceGraph.edges`; `refs` is one hop only |
| `--scope=affected`, `--kind=` filters on `missing` | `query_missing_v1.spl` | changed-set input from the git provider |
| `md` / `html` formats | `query_render_*_v1.spl` | `query_options_v1.spl` rejects all but table/sdn (~line 118) |
| Profiles other than `worktree` actually evaluated (index, push range, PR candidate, release) | `main.spl` capture branch | capture providers for each exact input; today `trace_capture_worktree_v1` only |
| Reverse-index cache + full/incremental parity spec (TRACE incremental fixtures) | `src/lib/common/traceability/incremental.spl` | cache design in plan 2.2 |
| MCP `simple_trace` tool | `src/app/mcp/` | stable SDN result schema for `missing` |
| Pre-push staged traceability check | `scripts/hooks/pre-commit` / push tier | `commit` profile must evaluate the Git index first (explicitly untouched here) |
| `TraceLinkStatus` members Tested/Stale/Blocked/NotApplicableReviewed are defined but never produced | `query_missing_v1.spl` | run-evidence and reviewed-exception inputs |
| `trace` registry line still says `list|show|refs` | `src/app/cli/command_registry*` (spec pins the current text) | update spec and registry together |

## Primitive id debt (not retyped here on purpose)
Existing public `text` ids that should become domain types: `TraceNode.id`, `TraceClaim.id/from_id/to_id/origin_id/rule_id/scope_id`,
`TraceEdge.id/from_id/to_id`, `TraceLocator.entity_id`, `TraceDiagnostic.subject_id/entity_id`,
`SnapshotSubject.snapshot_id/revision_id/tree_id`, `TraceCliOptionsV1.scope/progress`,
`TraceEvaluationV1.scope/profile/kind/qualification` (all `src/lib/common/traceability/model.spl`,
`qualification_types_v1.spl:19`), and `TraceMissingEntryV1.requirement_id`/`TraceMissingResultV1.snapshot_id` in the new file follow the same `text` convention for consistency.
Retyping needs a coordinated change of every decoder and spec; out of scope for one PR.
