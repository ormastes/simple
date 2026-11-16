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
- Relation orientation: for `implemented_by` and `verified_by` the REQUIREMENT is the `from` end (`schema.spl` `trace_endpoint_kinds_valid`). A requirement is linked to verification directly, through `decomposes_to` a criterion that has `accepted_by`/`verified_by`, or by a `--spec-root` `# @req` sidecar `verified_by` row.
- `trace missing` never emits `Verified` or `Tested`: it has no run evidence, so a structural verifying link is `Linked` (plan §6 separates linked/tested/verified). A requirement is omitted only when implementation and verification are both `Linked`.
- In an incomplete graph an absent link is `Unknown`, not `Missing`.
- Result structs use domain types (`TraceRequirementIdV1`, `TraceSnapshotIdV1`, `TraceRequirementCountV1`, `TraceGraphCompletenessV1`); `title` stays `text` as display text.

## Verify
`bin/simple test test/01_unit/app/cli/traceability_command_spec.spl test/01_unit/app/traceability/trace_node_query_spec.spl`
Manual: `bin/simple run src/app/traceability/query_main.spl missing --spec-root=test/01_unit`.

Open work: `doc/08_tracking/bug/trace_command_family_remaining_2026-11-14.md`.

## Domain types on the app API (primitive_api = 0, 2026-11-15)
`cli_options_v1.spl`, `structural_report_v1.spl`, `query_options_v1.spl`, `query_main.spl` carry no `primitive_api` finding. The lint scans `pub fn` signatures only (not struct fields), so the replacements are signature types:
- `trace_cli_options_validate_v1` returns `Result<TraceCliOptionsV1, text>` (the validated options), not `Result<bool, text>`.
- `trace_evaluate_captured_v1(.., max_diagnostics: TraceDiagnosticLimitV1)` and `trace_qualification_infrastructure_v1(.., snapshot_completeness: TraceSnapshotCompletenessV1, ..)` (enum `Complete | Incomplete`), both in `structural_report_v1.spl`; callers: `main.spl` (3 sites) and `test/03_system/app/traceability/feature/traceability_capture_limits_spec.spl`.
- `run_trace_query_v1` / `trace_query_error_exit_v1` return `TraceExitCodeV1 { value }`; the CLI router reads `.value` (`src/app/cli/_CliMain/main_and_help.spl`), `main()` passes `code.value` to `exit`. Exit codes: 0 rendered, 1 item not found, 2 incomplete graph or invalid (incomplete decided by `trace_query_completion_exit_v1` via `trace_command_verdict_v1`).
- `trace_query_sdn_requested_v1` returns enum `TraceQueryFormatV1 (Table | Sdn)`; `trace_query_format_parse_v1` is the strict parser (case-sensitive, no default) and backs `--format` validation with the same message; `trace_query_format_name_v1` gives the wire text.
- Spec: `test/01_unit/app/traceability/trace_app_domain_types_spec.spl` (adverse: `xml`, empty, `SDN`, bad scope/progress, malformed query exits 2).
- `TraceQueryOptionsV1` / `TraceCliOptionsV1` text fields (format, kind, scope, progress...) are unchanged: `doc/08_tracking/bug/trace_app_text_option_fields_2026-11-15.md`.
