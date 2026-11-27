# trace query prints TRACE-LEGACY-ROW / TRACE-AUTHORITY-CONFLICT diagnostics on stdout

- **Filed:** 2026-11-06 (libbug coordinator, Astra review of PRs #7202/#7206)
- **Status:** fixed (P3), 2026-11-08. The previously landed r12 repair has green
  trace-spec evidence; current source routes all non-SDN diagnostic batches to
  stderr. A fresh direct-query attempt was blocked before execution by the
  unrelated `windows_redirected_process.spl` parser defect.
- **Symptom:** `simple run src/app/traceability/query_main.spl refs ...` appends per-row
  diagnostics (8 `TRACE-LEGACY-ROW: row has N fields, expected 10` for malformed bug_db rows,
  `TRACE-AUTHORITY-CONFLICT` lines) to stdout after the table, mixing them with the result an
  agent parses.
- **Fix direction:** print diagnostics on stderr (or as one summary count line on stdout),
  and file the malformed bug_db rows themselves.

- **2026-11-06 fix (r12):** table mode prints one `Diagnostics: N (details on stderr)` line on stdout and the per-row lines on stderr (`query_main.spl` `query_diagnostics_to_stderr_v1`); SDN unchanged. Malformed bug_db rows reported (bugs table, field counts): bootstrap_stage2_backend_object_path_status_2026_09_08 (11), windows_bootstrap_cmp_authority_missing (11), stage3_hir_contract_model_partial_integration_2026_08_14 (11), text-split-limit-ignored (12), compiled_checker_parser_category_c_2026_08_03 (14), check_stage3_recovery_authority_arity_drift_2026_09_17 (11), llm_caret_parity_matrix_target_paths_use_hyphens_2026-08-24 (3), parse_claude_json_response_name_collision_2026-07-20 (5). bug_db.sdn not edited.
