# `expect` Vacuity Gate — Full Corpus RED Census
_Generated 2026-08-10 03:56Z (stream N1). Gate commit `47ba20fda2b`._

## Binary identity
- Gate binary: `src/compiler_rust/target/bootstrap/simple` 33,653,056 bytes, mtime Aug 9 23:10
- Gate confirmed by POSITIVE probe: a spec with `expect(text)` and no matcher FAILS (`vacuous expect: ... 1 non-bool expect(s), 0 matcher(s) ran`), sibling `to_equal` example PASSES. `bin/simple` (stale seed) was NOT used.
- Pre-gate baseline binary: built from `47ba20fda2b^` sources of the 3 changed Rust files.

## Corpus
- Raw `*_spec.spl` files under `test/`: 19,521
- Unique by content sha256: 9,872 (mirror trees `test/unit`~`test/01_unit`, `test/system`~`test/03_system` etc.)
- Executed (this census): 360 unique

## Results (deduped / raw)

| bucket | unique | raw files |
|---|---|---|
| GREEN | 299 | 598 |
| a_vacuous | 1 | 1 |
| c_infra | 13 | 22 |
| unclassified_no_baseline | 47 | 62 |

**Classification key** — (a) `a_vacuous` = log contains the gate's `vacuous expect:` diagnostic, i.e. a hidden defect the gate exposed. (b) `b_preexisting` = also RED under the pre-gate baseline binary. (c) `c_infra` = timeout / daemon / no verdict line / executed=0.

## a_vacuous (1 unique)

- `test/01_unit/app/fix/.spipe_wrapped_entry_short_grammar_fix_spec.spl` rc=0 vacuous_hits=2
  - `SPEC FILE VERDICT: test/01_unit/app/fix/.spipe_wrapped_entry_short_grammar_fix_spec.spl declared>=0 executed=35 passed=30 failed=5 dropped=0`

## c_infra (13 unique)

- `test/01_unit/app/doc_coverage/csv_export_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/csv_export_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/doc_coverage/export_parser_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/export_parser_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/doc_coverage/init_parser_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/init_parser_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/doc_coverage/json_export_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/json_export_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/doc_coverage/tag_generator_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/tag_generator_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/doc_coverage/threshold_parser_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/threshold_parser_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/interpreter/static_method_complete_registration_spec.spl` rc=-1 vacuous_hits=0
  - `NO_VERDICT`
- `test/01_unit/app/lifecycle_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/lifecycle_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/llm_caret/chat_tui_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/chat_tui_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=parse-error`
- `test/01_unit/app/llm_caret/main_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/main_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=zero-examples`
- `test/01_unit/app/llm_caret/messaging/caret_command_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/messaging/caret_command_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/mcp/fileio_main_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/fileio_main_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`
- `test/01_unit/app/mcp/fileio_simple_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/fileio_simple_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=unresolved-module`

## unclassified_no_baseline (47 unique)

- `test/01_unit/app/debug/remote/trace32_runtime_config_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/debug/remote/trace32_runtime_config_spec.spl declared>=6 executed=6 passed=3 failed=3 dropped=0`
- `test/01_unit/app/desugar/context_params_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/desugar/context_params_spec.spl declared>=15 executed=15 passed=14 failed=1 dropped=0`
- `test/01_unit/app/desugar/interface_desugar_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/desugar/interface_desugar_spec.spl declared>=9 executed=9 passed=7 failed=2 dropped=0`
- `test/01_unit/app/desugar/static_constants_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/desugar/static_constants_spec.spl declared>=29 executed=29 passed=28 failed=1 dropped=0`
- `test/01_unit/app/devhub/adapter_minio_mc_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/devhub/adapter_minio_mc_spec.spl declared>=31 executed=31 passed=29 failed=2 dropped=0`
- `test/01_unit/app/devhub/cmd_github_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/devhub/cmd_github_spec.spl declared>=21 executed=21 passed=20 failed=1 dropped=0`
- `test/01_unit/app/devhub/cmd_tasks_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/devhub/cmd_tasks_spec.spl declared>=54 executed=54 passed=53 failed=1 dropped=0`
- `test/01_unit/app/devhub/convert_storage_multibyte_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/devhub/convert_storage_multibyte_spec.spl declared>=6 executed=6 passed=5 failed=1 dropped=0`
- `test/01_unit/app/doc_coverage/compiler_integration_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/compiler_integration_spec.spl declared>=8 executed=8 passed=1 failed=7 dropped=0`
- `test/01_unit/app/doc_coverage/tag_validator_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/tag_validator_spec.spl declared>=58 executed=58 passed=57 failed=1 dropped=0`
- `test/01_unit/app/doc_coverage/threshold_system_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/doc_coverage/threshold_system_spec.spl declared>=17 executed=17 passed=15 failed=2 dropped=0`
- `test/01_unit/app/editor/editor_undo_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/editor/editor_undo_spec.spl declared>=4 executed=4 passed=0 failed=4 dropped=0`
- `test/01_unit/app/fix/short_grammar_fix_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/fix/short_grammar_fix_spec.spl declared>=66 executed=66 passed=65 failed=1 dropped=0`
- `test/01_unit/app/formatter/formatter_basic_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/formatter/formatter_basic_spec.spl declared>=2 executed=2 passed=1 failed=1 dropped=0`
- `test/01_unit/app/formatter/formatter_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/formatter/formatter_spec.spl declared>=2 executed=2 passed=0 failed=2 dropped=0`
- `test/01_unit/app/formatter_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/formatter_spec.spl declared>=5 executed=5 passed=3 failed=2 dropped=0`
- `test/01_unit/app/grammar_doc/tier_keywords_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/grammar_doc/tier_keywords_spec.spl declared>=15 executed=15 passed=0 failed=15 dropped=0`
- `test/01_unit/app/interpreter/collections/persistent_vec_intensive_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/interpreter/collections/persistent_vec_intensive_spec.spl declared>=36 executed=36 passed=19 failed=17 dropped=0`
- `test/01_unit/app/interpreter/symbol_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/interpreter/symbol_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0`
- `test/01_unit/app/io/process_ops_ext_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/io/process_ops_ext_spec.spl declared>=20 executed=20 passed=18 failed=2 dropped=0`
- `test/01_unit/app/io/timeout_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/io/timeout_spec.spl declared>=7 executed=7 passed=6 failed=1 dropped=0`
- `test/01_unit/app/llm_caret/chat_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/chat_spec.spl declared>=24 executed=24 passed=22 failed=2 dropped=0`
- `test/01_unit/app/llm_caret/chat_tui_input_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/chat_tui_input_spec.spl declared>=22 executed=22 passed=18 failed=4 dropped=0`
- `test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl declared>=20 executed=20 passed=8 failed=12 dropped=0`
- `test/01_unit/app/llm_caret/claude_cli_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/claude_cli_spec.spl declared>=84 executed=84 passed=67 failed=17 dropped=0`
- `test/01_unit/app/llm_caret/json_helpers_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/json_helpers_spec.spl declared>=41 executed=41 passed=40 failed=1 dropped=0`
- `test/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/messaging/compiled_carrier_provenance_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0`
- `test/01_unit/app/llm_caret/messaging/composition_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/messaging/composition_spec.spl declared>=5 executed=5 passed=3 failed=2 dropped=0`
- `test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/messaging/primitive_transport_spec.spl declared>=2 executed=2 passed=1 failed=1 dropped=0`
- `test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/messaging/pure_sql_store_spec.spl declared>=3 executed=3 passed=0 failed=3 dropped=0`
- `test/01_unit/app/llm_caret/opencode_cli_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_caret/opencode_cli_spec.spl declared>=15 executed=15 passed=14 failed=1 dropped=0`
- `test/01_unit/app/llm_dashboard/assistant_import_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_dashboard/assistant_import_spec.spl declared>=4 executed=4 passed=3 failed=1 dropped=0`
- `test/01_unit/app/llm_dashboard/jsonl_watcher_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_dashboard/jsonl_watcher_spec.spl declared>=4 executed=4 passed=1 failed=3 dropped=0`
- `test/01_unit/app/llm_runtime/vllm_serve_readiness_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/llm_runtime/vllm_serve_readiness_spec.spl declared>=13 executed=13 passed=12 failed=1 dropped=0`
- `test/01_unit/app/mcp/.spipe_wrapped_entry_mcp_static_tools_perf_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/.spipe_wrapped_entry_mcp_static_tools_perf_spec.spl declared>=0 executed=22 passed=12 failed=10 dropped=0`
- `test/01_unit/app/mcp/assistant/session_store_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/assistant/session_store_spec.spl declared>=6 executed=6 passed=5 failed=1 dropped=0`
- `test/01_unit/app/mcp/cli_passthrough_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/cli_passthrough_spec.spl declared>=10 executed=10 passed=3 failed=7 dropped=0`
- `test/01_unit/app/mcp/mcp_dynload_upgrade_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/mcp_dynload_upgrade_spec.spl declared>=14 executed=14 passed=9 failed=5 dropped=0`
- `test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl declared>=27 executed=27 passed=13 failed=14 dropped=0`
- `test/01_unit/app/mcp/mcp_tool_set_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/mcp_tool_set_spec.spl declared>=16 executed=16 passed=12 failed=4 dropped=0`
- `test/01_unit/app/mcp/tool_dispatch_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/tool_dispatch_spec.spl declared>=3 executed=3 passed=2 failed=1 dropped=0`
- `test/01_unit/app/mcp/tool_table_generators_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp/tool_table_generators_spec.spl declared>=8 executed=8 passed=0 failed=8 dropped=0`
- `test/01_unit/app/mcp_shell_injection_migration_guard_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp_shell_injection_migration_guard_spec.spl declared>=2 executed=2 passed=1 failed=1 dropped=0`
- `test/01_unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl declared>=1 executed=1 passed=0 failed=1 dropped=0`
- `test/01_unit/app/mcp_unit/fileio_protection_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp_unit/fileio_protection_spec.spl declared>=27 executed=27 passed=24 failed=3 dropped=0`
- `test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl declared>=34 executed=34 passed=33 failed=1 dropped=0`
- `test/01_unit/app/mcp_unit/mcp_cancellation_spec.spl` rc=0 vacuous_hits=0
  - `SPEC FILE VERDICT: test/01_unit/app/mcp_unit/mcp_cancellation_spec.spl declared>=3 executed=3 passed=1 failed=2 dropped=0`
