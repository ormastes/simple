# Compiler unit sweep (seed-run) 2026-11-12: open items that need an owner

**Status:** open. **Found by:** the compiler unit-spec sweep on `release/1.0.0` at
`c2c31adeb06`. **Evidence class:** seed-run only. The runs used the Rust seed's
`test` command (`pinned-bfe789dd4118`); no pure-Simple full CLI is deployed on
this host yet. Re-check every item once one exists.

The stale source-pin specs were retargeted in a separate PR. The items below
were deliberately **not** "fixed" in a spec. In each case the spec pins an
invariant that current source contradicts, or the failure is outside the
code/spec, so a retarget would be weakening the assertion.

## Owner decisions (spec invariant vs current source)

| spec | failure | finding |
|---|---|---|
| `bootstrap/stage4_streaming_surfaces_contract_spec.spl` | `expected 20854 to be less than 20000` | `src/compiler/70.backend/backend/interpreter_binop.spl` grew past its 20000-byte budget. The budget was not raised; either split the file or raise the budget by owner decision. |
| `bootstrap/stage4_unlimited_streaming_ownership_spec.spl` | `low_memory` present in the streaming selector | a528caf4937 added `driver_low_memory_streaming_requested_values(ctx.options.low_memory, ...)` as an extra OR route in `driver_streaming_surface_route` (`src/compiler/80.driver/driver_phase_gates.spl:87`). The spec requires selection to be independent of low-memory policy. |
| `bootstrap/stage4_fix_tool_sync_entry_spec.spl` | file `src/compiler/tools/fix/main.spl` missing | The only fix CLI on the tree is `src/compiler/90.tools/fix/main.spl`, and it is `async fn main() -> Int` with `dry_run: Bool` and `.slice(`. That is exactly the shape the spec forbids, so retargeting the path would leave the spec red. |
| `bootstrap/specialized_template_context_contract_spec.spl` | both pinned files missing | ab9305d783e (40.mono removal) deleted `linker/linker_context.spl`, `pipeline/compiler_context.spl` and the specialization hooks. The spec pins a removed feature; deleting it needs owner approval. |
| `bootstrap/stage2_capability_stage4_guard_spec.spl` | `SIMPLE_BOOTSTRAP_STAGE4=0`, "Stage 4 remains bound to verified Stage 3" missing | `scripts/bootstrap/bootstrap-from-scratch.sh:6247-6290` still prints `using seed for stage 4` on a failed Stage 2 capability probe. Owned by the bootstrap-script lane; not touched here. |
| `bootstrap/hir_statement_shared_binding_contract_spec.spl` | `var rt_hir: HirExpr? = nil` + reassignment | 064d40e5896 introduced this shape at `src/compiler/20.hir/hir_lowering/statements.spl:1077`. It is a native-lane workaround (`match rt_val: case Some` never matched), and the spec forbids it. Decide between the spec and the workaround. |
| `bootstrap/stage4_streaming_surfaces_contract_spec.spl` (2 of 4 tests) | `SIMPLE_STAGE3_STREAMING_SURFACES=1` missing | a1d66e52206 flipped Stage 3 streaming to `=0` at `scripts/bootstrap/bootstrap-from-scratch.sh:4738,:5876`, and the worker scripts also set `=0` (`stage3-native-build-worker.sh:163`, `resume-stage3-from-admitted.sh:995`). The commit message gives no reason. Retargeting would flip the invariant. |
| `bootstrap/newunit_pool_reset_contract_spec.spl` (3 tests) | `newunit_project_*`, `builder_owner.add_surface(`, `parse_all_legacy_impl` missing | These symbols exist nowhere in `src/`, and `git log -S` finds no commit that ever added them. The spec arrived in the mass merge e274cd33719, describing an API that never landed (`units_newunit_registry_spec.spl:29-33` imports them too). Implement the API or delete the spec. |
| `bootstrap/stage4_cli_ops_stderr_facade_spec.spl` | `stderr_write` facade missing | `src/app/io/cli_ops.spl:127-128` is still `fn _cli_eprint(msg: text): eprint(msg)`; the canonical-stderr routing was never implemented. |

## Environment (d)

| spec | failure | finding |
|---|---|---|
| `bootstrap/llvm_aggregate_shared_binding_contract_spec.spl` (2 tests) | `expected -1 to equal 0` | It spawns `bin/simple compile`, and a fresh worktree has no `bin/simple` (exit -1). Needs a deployed full CLI. |
| `95.interp/interpreter/*` (10 files, 27 tests) | `expected 126 to equal 0` / `false to equal true` | They spawn `bin/simple` through `process_run_timeout`, which a fresh worktree does not have (exit 126). Needs a deployed full CLI. |

## Resolved since filing

- `bootstrap/entry_package_facade_precedence_spec.spl`: a spec bug. The fixture string `".variables.{env_get_or}"` was unescaped interpolation (#8561).
- `30.types/cfg_decl_check_spec.spl` and `50.mir/entry_closure_imported_class_probe_symbols_spec.spl`: private functions were imported across modules (`empty_type_env`, `empty_subst_map`, `probe_events_len`); they are now `pub` (#8558).
- `50.mir/closure_capture_write_spec.spl` and `closure_capture_write_forms_spec.spl` (23 tests): the plain `name = expr` statement fast path (c1fdb67f5fe) created its target and STMT_ASSIGN with span 0, so the captured-write diagnostic lost its line (#8603).
- `50.mir/compound_assignment_operator_mapping_spec.spl`, `enum_match_divergence_spec.spl`, `nul_literal_raw_constructor_operand_spec.spl`, and 1 of 3 in `for_in_runtime_tuple_decode_spec.spl`: these specs were stale (#8602).
- `50.mir/struct_ctor_field_local_spec.spl`, `mir_option_result_qualified_field_spec.spl` and `user_enum_discriminant_positional_spec.spl`: these specs were stale (#8614).

## Real source bug, not fixed here

- `20.hir/export_origin_generated_comment_foreign_package_spec.spl` ("does not fail a package sibling that prebinds the facade's exports"). The staged `[W-HIR-UNDECL-IMPORT-001]` diagnostic, added by 54356c20894 at `src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:1105-1112`, also fires on the implicit package-sibling glob prebind (`register_package_sibling_symbols`, `module_import_resolution.spl:158`). The message there names a `use pkg.runtime.{...}` that the importer never wrote. The diagnostic was meant for braced imports only, so it needs to know whether it is running under glob expansion. Owner: the 54356c20894 lane.

## Probably owned elsewhere

- `50.mir/mir_verify/mir_verify_rule_registry_spec.spl`: `config/compiler/mir_verify_rules.sdn` parses, but its `rules:` block sequence of maps comes back with 0 rows (the spec expects 18). The SDN block-sequence parsing in `src/lib/common/sdn/parser.spl` was being edited in the shared checkout at the time.

## Not yet triaged (behavioural; need a focused run)

- `20.hir/bootstrap_regressions/unresolved_name_eager_resolution_spec.spl` (2 tests). A name declared in a never-imported sibling module produces no `unresolved name` error.
- `30.types/written_any_compile_mode_spec.spl` (1). The `assert_equal` failure carries no step detail.
- 50.mir, rest of the sweep (seed-run at `88a17aa6e20`): these files still fail and are not fixed:
  - `for_in_runtime_tuple_decode` (2 tests, struct elements bound by value);
  - `generic_self_method_result_ctor`;
  - `generic_struct_field_instance_paths`;
  - `generic_type_param_eq_hash_lowering`;
  - `stage2_generic_class_receiver` (`expected other to equal named1`);
  - `result_enum_payload_record_provenance`;
  - `result_err_generic_original_binder`;
  - `provider_method_demand_determinism`;
  - `imported_struct_operator_owner`;
  - `mir_provider_trait_impl_once_per_closure_prevention`;
  - `typed_u64_push_layout` (2 tests);
  - `bare_variant_retained_subject`;
  - `bootstrap_cli_named_array_index`;
  - `builtin_method_extras_guard`;
  - `compile_error_owner_layout`;
  - `any_index_read`;
  - the hwir riscv projections (`control_projection`, `lsu_projection`, `completion_skid`);
  - `hwir_riscv_scalar_decoder` (0 examples executed).
- **Not hangs:** `50.mir/flat_pool_reader_mir_lowering_spec.spl` passes 3/3 alone but takes 367s (CPU-bound, flat RSS of about 1.1 GB; it MIR-lowers the real `flat_pool_codec.spl`). `50.mir/mir_receiver_shapes_spec.spl` passes 7/7 alone in 20s. Both were only still running when their 1800s chunks timed out. flat_pool is a perf item, not a hang.
- **Specs that import a non-exported helper:** the seed now hard-errors (`error: semantic: private fn ... is not visible to <spec>`), so the whole file runs 0 examples. Affected specs:
  - `60.mir_opt/general_patterns_spec` (`clib_parity_rule_is_general`, `clib_parity_domain_rule_count`, and more, reported one per run);
  - `60.mir_opt/string_builder_opt_spec` (`string_builder_opt_run_on_function`, `string_builder_opt_enabled_for`);
  - `70.backend/cranelift_ssa_phi_nary_slot_spec` (`cranelift_ssa_phi_dest_ids`, `cranelift_local_slot_sizes`);
  - `99.loader/module_loader_mangle_owner_spec` (`mangle_name`);
  - `50.mir/any_index_read_spec` (`create_collection_opt_pass`).

  Some of these functions are genuinely cross-module and should be `pub`: `string_builder_opt_run_on_function` is called from `mir_opt/mod.spl`, and `clib_parity_rule_is_general` is export-used by `pattern/__init__.spl`. Others are test-only internals, where the choice between `pub` and a test-facing API is the owner's. A two-function `pub` fix was not enough to make either 60.mir_opt spec run, so none is proposed here.
- **Seed misattribution:** in `50.mir/try_struct_payload_field_for_in_spec.spl` the seed reports private `result_err_field_type_key_v2` (`50.mir/_MirLoweringExpr/result_err_record_owner.spl`) as "not visible to `00.common/dependency/member_visibility.spl`". The function is only called inside its own module, so this is likely a seed interpreter (c) caller-module tracking bug.
- `80.driver`: 5 failures, including:
  - `compiler_driver_identity_release_spec`: `compiler.driver` does not export `driver_hir_archive_production_controller_v1`, an archive symbol removed with 40.mono;
  - `nonvacuity_receipts_acceptance_spec`;
  - `shs_exit_hygiene_acceptance_spec`.

  All three look like stale source pins.
## Side finding

`src/app/io/_CliCompile/native_build.spl:197` `_nb_resolve_segs` keeps its own
10-entry tier list in a non-canonical order (`nogc_async_immut` before
`nogc_sync_mut`). No `.spl` file imports that module. Either delete it or make
it use `source_root_std_family_order_v1()`.
