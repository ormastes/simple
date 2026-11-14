# Feature expert: trace command family (profile + missing)

Scope of this slice: `traceability-check --profile=<name>` and `trace missing`.
Plan: `simple_traceability_spipe_bug_mcp_skills_improvement_plan_2026-11-14.md` section 6 (6.1 CLI, 6.4 profiles), fixtures TRACE-003/004/005.

## Where things live
| Concern | File |
| --- | --- |
| Closed profile set (`TraceProfile`, parse, canonical names) | `src/lib/common/traceability/profile_v1.spl` |
| Decoder accepts every profile name (derived from the enum) | `src/lib/common/traceability/qualification_v1.spl` |
| `--profile` flag, default `worktree`, unknown name = usage error (exit 2) | `src/app/traceability/cli_options_v1.spl` |
| Evaluation profile threading, `trace_qualification_profile_unavailable_v1` | `src/app/traceability/structural_report_v1.spl` |
| CLI wiring (non-worktree profile => incomplete, exit 2) | `src/app/traceability/main.spl` |
| `trace missing` pure query + `TraceLinkStatus` | `src/lib/common/traceability/query_missing_v1.spl` |
| `trace missing` options / render / dispatch | `query_options_v1.spl`, `query_render_missing_v1.spl`, `query_main.spl` (all `src/app/traceability/`) |

## Contracts to keep
- No `--profile` means `worktree` and byte-identical output to before (spec: "keeps the default evaluation").
- Exit codes: 0 satisfied, 1 violations, 2 incomplete or usage error. Only `worktree` is evaluated; every other profile reports `TRC-PROFILE-UNAVAILABLE` with exit 2 because the producer captures the working tree only. Never certify a profile from the wrong input.
- Relation orientation: for `implemented_by` and `verified_by` the REQUIREMENT is the `from` end (`schema.spl` `trace_endpoint_kinds_valid`). A requirement is verified directly, through `decomposes_to` a criterion that has `accepted_by`/`verified_by`, or by a `--spec-root` `# @req` sidecar `verified_by` row.
- In an incomplete graph an absent link is `Unknown`, not `Missing`.
- New public fns avoid bare `i64`/`bool` (primitive_api lint); counts live in struct fields.

## Verify
`bin/simple test test/01_unit/app/cli/traceability_command_spec.spl test/01_unit/app/traceability/trace_node_query_spec.spl`
Manual: `bin/simple run src/app/traceability/query_main.spl missing --spec-root=test/01_unit`.

Open work: `doc/08_tracking/bug/trace_command_family_remaining_2026-11-14.md`.
