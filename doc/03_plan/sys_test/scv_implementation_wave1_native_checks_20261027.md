# First-wave native verification inventory

Status: NOT RUN. This is a required-check inventory, not an execution receipt.

Use one exact admitted full CLI/runtime/provider identity. Record its hash, stage, provenance/admission receipts and supported commands separately from the tested feature revision. Stage 2/3 and Rust-seed bootstrap results cannot substitute for general SPipe/docgen/core/MCP evidence.

The source-only candidate remains unfinished until actual tests, required native smoke, manuals, maintenance and relevant coverage pass. Follow the [native test workflow](../../07_guide/infra/testing/native_test_binary_workflow.md). Use ordered repeated `--native-source` overlays where required and record the actual backend; bare `--native` is unsupported. The LLVM producer preflight failed because no shared provider was installed; a Cranelift Stage 2 producer is being attempted separately. No LLVM execution is implied.

## Changed executable specifications

Run each applicable exact-subject scenario once. A failure repair invalidates only the affected evidence; preserve unchanged passing results. Existing source-contract tests are source wiring evidence, not substitutes for the cold/warm/native semantics oracles.

- `test/01_unit/app/scv/config_commands_spec.spl` — NOT RUN
- `test/01_unit/compiler/bootstrap/entry_closure_physical_source_dedup_spec.spl` — NOT RUN
- `test/01_unit/compiler/bootstrap/module_surface_canonical_once_spec.spl` — NOT RUN
- `test/01_unit/compiler/bootstrap/module_surface_promote_definition_spec.spl` — NOT RUN
- `test/01_unit/compiler/bootstrap/newunit_pool_reset_contract_spec.spl` — NOT RUN
- `test/01_unit/compiler/bootstrap/stage4_streaming_surfaces_contract_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/compiler_driver_type_owner_contract_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/ctx_verdict_stale_receiver_call_sweep_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/hir_adopt_and_streaming_parse_receipts_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/hir_shard_failure_counters_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/nonstreaming_parse_owner_prep_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/parse_shard_execution_mode_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/parse_shard_slim_entry_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/phase2_parallel_safety_contract_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/plain_parse_loop_progress_contract_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/stage3_promotion_batch_contract_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/stage3_streaming_route_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/tldr_frozen_production_route_spec.spl` — NOT RUN
- `test/01_unit/compiler/driver/tldr_route_spec.spl` — NOT RUN
- `test/01_unit/compiler/frontend/environment_variant_frontend_policy_binding_v1_spec.spl` — NOT RUN
- `test/01_unit/compiler/frontend/persistent_parse_owner_contract_spec.spl` — NOT RUN
- `test/01_unit/compiler/hir/hir_unresolved_name_import_reachability_spec.spl` — NOT RUN
- `test/01_unit/compiler/hir/module_surface_promote_reason_spec.spl` — NOT RUN
- `test/01_unit/lib/common/io/read_only_file_view_bounded_beneath_v1_spec.spl` — NOT RUN
- `test/01_unit/lib/scv/scv_config_v1_spec.spl` — NOT RUN
- `test/01_unit/lib/scv/snapshot_v1_adapter_spec.spl` — NOT RUN
- `test/01_unit/lib/scv/snapshot_v2_source_witness_spec.spl` — NOT RUN
- `test/01_unit/lib/scv/storage_failure_spec.spl` — NOT RUN
- `test/02_integration/app/scv_tag_publication_failure_spec.spl` — NOT RUN
- `test/02_integration/compiler/facet_manifest_parser_context_spec.spl` — NOT RUN
- `test/02_integration/lib/scv/db_schema_v2_spec.spl` — NOT RUN
- `test/02_integration/lib/scv/solver_db_rows_host_v1_spec.spl` — NOT RUN
- `test/03_system/app/scv/feature/scv_config_command_spec.spl` — NOT RUN
- `test/03_system/app/scv/feature/scv_config_v1_spec.spl` — NOT RUN
- `test/03_system/app/scv/feature/scv_db_schema_solver_host_v1_spec.spl` — NOT RUN
- `test/03_system/app/scv/feature/scv_solver_host_v1_spec.spl` — NOT RUN
- `test/03_system/app/scv/feature/scv_storage_publication_spec.spl` — NOT RUN
- `test/integration/app/scv_filebuffer_status_spec.spl` — NOT RUN

## Required common gates

- `<runtime> check src/compiler`
- `<runtime> check src/lib`
- `<runtime> check src/app/mcp`
- `<runtime> check src/app/simple_lsp_mcp`
- `SIMPLE_LIB=src <runtime> test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`
- Core runtime and native MCP/LSP smoke against the integration subject, using the admitted toolset/receipt route. A producer-baseline toolset smoke is prerequisite evidence, not feature-revision smoke.
- Generate/review each changed scenario manual with `<runtime> spipe-docgen <spec> --output doc/06_spec --no-index`; require zero stubs.
- Run `<runtime> sspec-maintain scan <spec>` once for each changed SSpec/manual pair; review all seven scores and actual findings.
- Collect required meaningful branch-coverage evidence on changed owners. No source assertion count is coverage.
- Working/staged direct-env guards, executable-spec layout, whitespace and exact-head higher-model review before landing.

No npm/package publication path is changed by this first wave. Add the isolated package/native-server build gates if that scope changes. All 65 master tasks and all 115 selected acceptance scenarios remain in scope for the full goal; the list above is only this wave's changed-file inventory.
