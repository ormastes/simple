# Duplicate test-tree merge worklist (legacy ahead of numbered)

**Status:** OPEN — worklist, no action taken
**Found:** 2026-08-09 by stream I4 (duplicate-tree investigation)
**Component:** `test/**`

## Why this file exists

`test/` carries TWO parallel trees: numbered (`test/01_unit`, `test/03_system`, …)
and legacy (`test/unit`, `test/system`, …). They are NOT byte-identical — the
common assumption that they are is false and would make a delete-legacy sweep
destructive.

**Both trees execute.** `src/app/test_runner_new/` has no path allowlist and no
legacy exclusion; the default root is `test/` (`test_runner_main.spl:209`),
recursive. Every duplicated spec runs twice, so full-suite counts and timings
are inflated by roughly the overlap (~5,500 files).

`test/FILE.md` lists ONLY the numbered dirs in its Allowed Entries table, so the
legacy dirs are undeclared migration residue, not a deliberate compat path.
(The manifest guard is evidently not enforcing on `test/`.)

## Overlap

| numbered | legacy | shared | identical | divergent | only-numbered | only-legacy |
|---|---|---|---|---|---|---|
| `test/01_unit` | `test/unit` | 5096 | 4253 | 843 | 2490 | 7 |
| `test/03_system/feature` | `test/feature` | 367 | 286 | 81 | 404 | 2 |
| `test/02_integration` | `test/integration` | 633 | 544 | 89 | 181 | 0 |
| `test/03_system` | `test/system` | 349 | 287 | 62 | 3168 | 1589 |
| `test/05_perf` | `test/perf` | 128 | 110 | 18 | 77 | 7 |
| `test/04_smoke` | `test/smoke` | 1 | 1 | 0 | 6 | 0 |

~1,093 divergent pairs. Numbered longer in 571, **legacy longer in 145**,
equal-length-but-different in 364.

## DO NOT mechanically delete the legacy tree

145 legacy files are AHEAD of their numbered twin, and ~1,600 legacy-only paths
exist. A filename-heuristic sweep drops all of it — the documented "residue
sweeps delete load-bearing fixtures" failure.

Some numbered twins are STUBS: e.g. `test/01_unit/app/diagram/filter_spec.spl`
is 11 lines against a 199-line legacy original. Line-count ratio is the triage
signal — a large ratio means the numbered copy is a placeholder, not a revision.

## Correct sequence

1. Merge the 145 legacy-ahead files below into the numbered tree.
2. Triage the ~1,600 legacy-only paths.
3. Re-hash to prove 100% identity.
4. Delete legacy with `sh scripts/check/check-tree-size-push.shs --expect-files <n>`.

Equal-length-but-different pairs (364) still need a content diff — same length
does not mean same content.

## Worklist: legacy ahead of numbered (145)

Format: `legacy (lines) > numbered (lines)`. Sorted by the original scan order.

```
test/unit/app/diagram/filter_spec.spl (199) > test/01_unit/app/diagram/filter_spec.spl (11)
test/unit/app/doc_coverage/inline_comment_coverage_spec.spl (341) > test/01_unit/app/doc_coverage/inline_comment_coverage_spec.spl (339)
test/unit/app/doc/public_check/statistics_spec.spl (241) > test/01_unit/app/doc/public_check/statistics_spec.spl (19)
test/unit/app/doc/public_check/warnings_spec.spl (256) > test/01_unit/app/doc/public_check/warnings_spec.spl (16)
test/unit/app/formatter/formatter_basic_spec.spl (170) > test/01_unit/app/formatter/formatter_basic_spec.spl (16)
test/unit/app/formatter/formatter_comprehensive_spec.spl (1026) > test/01_unit/app/formatter/formatter_comprehensive_spec.spl (17)
test/unit/app/formatter/formatter_spec.spl (395) > test/01_unit/app/formatter/formatter_spec.spl (14)
test/unit/app/formatter_spec.spl (395) > test/01_unit/app/formatter_spec.spl (75)
test/unit/app/io/cli_ops_handlers_spec.spl (75) > test/01_unit/app/io/cli_ops_handlers_spec.spl (64)
test/unit/app/io/file_shell_exec_spec.spl (87) > test/01_unit/app/io/file_shell_exec_spec.spl (49)
test/unit/app/llm_caret/claude_api_spec.spl (293) > test/01_unit/app/llm_caret/claude_api_spec.spl (189)
test/unit/app/llm_caret/openai_api_spec.spl (300) > test/01_unit/app/llm_caret/openai_api_spec.spl (213)
test/unit/app/llm_caret/server_spec.spl (269) > test/01_unit/app/llm_caret/server_spec.spl (112)
test/unit/app/package/ffi_spec.spl (160) > test/01_unit/app/package/ffi_spec.spl (21)
test/unit/app/package/package_spec.spl (390) > test/01_unit/app/package/package_spec.spl (41)
test/unit/app/svllm_pack/main_spec.spl (44) > test/01_unit/app/svllm_pack/main_spec.spl (41)
test/unit/app/test_runner_new/test_config_spec.spl (86) > test/01_unit/app/test_runner_new/test_config_spec.spl (66)
test/unit/app/test_runner_new/test_runner_args_ci_spec.spl (44) > test/01_unit/app/test_runner_new/test_runner_args_ci_spec.spl (35)
test/unit/app/todo/todo_parser_spec.spl (5) > test/01_unit/app/todo/todo_parser_spec.spl (3)
test/unit/app/tooling/color_utils_spec.spl (232) > test/01_unit/app/tooling/color_utils_spec.spl (18)
test/unit/app/tooling/command_dispatch_spec.spl (820) > test/01_unit/app/tooling/command_dispatch_spec.spl (805)
test/unit/app/tooling/coverage_ffi_spec.spl (288) > test/01_unit/app/tooling/coverage_ffi_spec.spl (18)
test/unit/app/tooling/coverage_threshold_spec.spl (97) > test/01_unit/app/tooling/coverage_threshold_spec.spl (30)
test/unit/app/tooling/test_db_edge_cases_spec.spl (317) > test/01_unit/app/tooling/test_db_edge_cases_spec.spl (25)
test/unit/app/tooling/test_runner_simple_spec.spl (571) > test/01_unit/app/tooling/test_runner_simple_spec.spl (519)
test/unit/app/tooling/test_stats_spec.spl (263) > test/01_unit/app/tooling/test_stats_spec.spl (19)
test/unit/app/ui/backend_matrix_spec.spl (197) > test/01_unit/app/ui/backend_matrix_spec.spl (115)
test/unit/baremetal/riscv/fpga_boot_linux_spec.spl (201) > test/01_unit/baremetal/riscv/fpga_boot_linux_spec.spl (200)
test/unit/browser_engine/net/cookie_store_spec.spl (495) > test/01_unit/browser_engine/net/cookie_store_spec.spl (344)
test/unit/compiler/backend/llvm_ir_builder_spec.spl (152) > test/01_unit/compiler/backend/llvm_ir_builder_spec.spl (64)
test/unit/compiler/blocks/builder_api_basic_spec.spl (123) > test/01_unit/compiler/blocks/builder_api_basic_spec.spl (122)
test/unit/compiler/blocks/builder_default_parser_spec.spl (22) > test/01_unit/compiler/blocks/builder_default_parser_spec.spl (21)
test/unit/compiler/blocks/easy_api_basic_spec.spl (62) > test/01_unit/compiler/blocks/easy_api_basic_spec.spl (61)
test/unit/compiler/blocks/testing_framework_spec.spl (93) > test/01_unit/compiler/blocks/testing_framework_spec.spl (92)
test/unit/compiler/blocks/utils_basic_spec.spl (134) > test/01_unit/compiler/blocks/utils_basic_spec.spl (133)
test/unit/compiler_core/annotation_intrinsics_spec.spl (93) > test/01_unit/compiler_core/annotation_intrinsics_spec.spl (32)
test/unit/compiler_core/ast_clone_spec.spl (145) > test/01_unit/compiler_core/ast_clone_spec.spl (43)
test/unit/compiler_core/exhaustiveness_spec.spl (120) > test/01_unit/compiler_core/exhaustiveness_spec.spl (41)
test/unit/compiler_core/file_class_introspection_spec.spl (154) > test/01_unit/compiler_core/file_class_introspection_spec.spl (41)
test/unit/compiler_core/generic_syntax_spec.spl (195) > test/01_unit/compiler_core/generic_syntax_spec.spl (42)
test/unit/compiler_core/ignored_return_warning_spec.spl (147) > test/01_unit/compiler_core/ignored_return_warning_spec.spl (35)
test/unit/compiler_core/mir_spec.spl (103) > test/01_unit/compiler_core/mir_spec.spl (37)
test/unit/compiler_core/mixin_expr_spec.spl (136) > test/01_unit/compiler_core/mixin_expr_spec.spl (33)
test/unit/compiler_core/must_use_spec.spl (157) > test/01_unit/compiler_core/must_use_spec.spl (40)
test/unit/compiler_core/traits_compiles_spec.spl (94) > test/01_unit/compiler_core/traits_compiles_spec.spl (32)
test/unit/compiler_core/traits_extended_spec.spl (213) > test/01_unit/compiler_core/traits_extended_spec.spl (45)
test/unit/compiler_core/traits_module_spec.spl (152) > test/01_unit/compiler_core/traits_module_spec.spl (27)
test/unit/compiler_core/traits_spec.spl (252) > test/01_unit/compiler_core/traits_spec.spl (46)
test/unit/compiler/custom_blocks_easy_api_spec.spl (405) > test/01_unit/compiler/custom_blocks_easy_api_spec.spl (402)
test/unit/compiler/frontend/required_comment_parse_spec.spl (222) > test/01_unit/compiler/frontend/required_comment_parse_spec.spl (221)
test/unit/compiler/linker/lib_smf_writer_spec.spl (100) > test/01_unit/compiler/linker/lib_smf_writer_spec.spl (97)
test/unit/compiler/linker/platform_defaults_spec.spl (206) > test/01_unit/compiler/linker/platform_defaults_spec.spl (170)
test/unit/compiler/mono/monomorphize_integration_spec.spl (115) > test/01_unit/compiler/mono/monomorphize_integration_spec.spl (114)
test/unit/compiler/native/x86_64_simd_spec.spl (349) > test/01_unit/compiler/native/x86_64_simd_spec.spl (255)
test/unit/compiler/parser/match_empty_array_bug_spec.spl (190) > test/01_unit/compiler/parser/match_empty_array_bug_spec.spl (189)
test/unit/compiler/parser/pub_enum_with_attribute_spec.spl (46) > test/01_unit/compiler/parser/pub_enum_with_attribute_spec.spl (36)
test/unit/compiler/semantics/lint/required_comment_lint_spec.spl (389) > test/01_unit/compiler/semantics/lint/required_comment_lint_spec.spl (388)
test/unit/compiler_shared/diagnostics/diagnostic_spec.spl (254) > test/01_unit/compiler_shared/diagnostics/diagnostic_spec.spl (24)
test/unit/compiler_shared/diagnostics/label_spec.spl (58) > test/01_unit/compiler_shared/diagnostics/label_spec.spl (21)
test/unit/compiler_shared/diagnostics/severity_spec.spl (124) > test/01_unit/compiler_shared/diagnostics/severity_spec.spl (24)
test/unit/compiler_shared/diagnostics/span_spec.spl (116) > test/01_unit/compiler_shared/diagnostics/span_spec.spl (23)
test/unit/compiler/types/platform_layout_attribute_spec.spl (227) > test/01_unit/compiler/types/platform_layout_attribute_spec.spl (156)
test/unit/compiler/u32_array_index_shr_spec.spl (142) > test/01_unit/compiler/u32_array_index_shr_spec.spl (135)
test/unit/core/parser_ce_keyword_identifier_spec.spl (118) > test/01_unit/core/parser_ce_keyword_identifier_spec.spl (92)
test/unit/gpu/graphics_3d_session_managed_backend_spec.spl (387) > test/01_unit/gpu/graphics_3d_session_managed_backend_spec.spl (386)
test/unit/lib/common/collections_spec.spl (299) > test/01_unit/lib/common/collections_spec.spl (298)
test/unit/lib/common/color_utils_rgb_hsl_spec.spl (467) > test/01_unit/lib/common/color_utils_rgb_hsl_spec.spl (26)
test/unit/lib/common/compress/gzip_spec.spl (205) > test/01_unit/lib/common/compress/gzip_spec.spl (204)
test/unit/lib/common/context_spec.spl (110) > test/01_unit/lib/common/context_spec.spl (30)
test/unit/lib/common/crypto/lshr2_debug_spec.spl (32) > test/01_unit/lib/common/crypto/lshr2_debug_spec.spl (28)
test/unit/lib/common/crypto/lshr3_debug_spec.spl (23) > test/01_unit/lib/common/crypto/lshr3_debug_spec.spl (20)
test/unit/lib/common/exp/artifact_spec.spl (77) > test/01_unit/lib/common/exp/artifact_spec.spl (14)
test/unit/lib/common/exp/config_spec.spl (163) > test/01_unit/lib/common/exp/config_spec.spl (14)
test/unit/lib/common/exp/run_spec.spl (111) > test/01_unit/lib/common/exp/run_spec.spl (15)
test/unit/lib/common/exp/storage_spec.spl (90) > test/01_unit/lib/common/exp/storage_spec.spl (14)
test/unit/lib/common/exp/sweep_spec.spl (150) > test/01_unit/lib/common/exp/sweep_spec.spl (17)
test/unit/lib/common/hooks/hook_registry_spec.spl (181) > test/01_unit/lib/common/hooks/hook_registry_spec.spl (39)
test/unit/lib/common/mock_phase4_spec.spl (610) > test/01_unit/lib/common/mock_phase4_spec.spl (609)
test/unit/lib/common/mock_phase6_spec.spl (1033) > test/01_unit/lib/common/mock_phase6_spec.spl (1032)
test/unit/lib/common/mock_phase7_spec.spl (1174) > test/01_unit/lib/common/mock_phase7_spec.spl (1156)
test/unit/lib/common/newline_constants_spec.spl (116) > test/01_unit/lib/common/newline_constants_spec.spl (21)
test/unit/lib/common/pure/data_loader_spec.spl (111) > test/01_unit/lib/common/pure/data_loader_spec.spl (21)
test/unit/lib/common/result_ce_spec.spl (187) > test/01_unit/lib/common/result_ce_spec.spl (185)
test/unit/lib/common/string_core_ops_spec.spl (772) > test/01_unit/lib/common/string_core_ops_spec.spl (764)
test/unit/lib/common/string_core_spec.spl (186) > test/01_unit/lib/common/string_core_spec.spl (21)
test/unit/lib/common/torch/torch_device_placement_status_spec.spl (117) > test/01_unit/lib/common/torch/torch_device_placement_status_spec.spl (96)
test/unit/lib/common/zstd_fse_weights_spec.spl (131) > test/01_unit/lib/common/zstd_fse_weights_spec.spl (125)
test/unit/lib/common/zstd_sequence_fse_execution_spec.spl (425) > test/01_unit/lib/common/zstd_sequence_fse_execution_spec.spl (401)
test/unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl (294) > test/01_unit/lib/crypto/aes128_ccm_rfc3610_kat_spec.spl (285)
test/unit/lib/crypto/ed25519_rfc8032_spec.spl (250) > test/01_unit/lib/crypto/ed25519_rfc8032_spec.spl (249)
test/unit/lib/crypto/sha256_x4_spec.spl (236) > test/01_unit/lib/crypto/sha256_x4_spec.spl (235)
test/unit/lib/driver/driver_manifest_test.spl (150) > test/01_unit/lib/driver/driver_manifest_test.spl (148)
test/unit/lib/driver/null_block_driver_test.spl (79) > test/01_unit/lib/driver/null_block_driver_test.spl (77)
test/unit/lib/editor/extension_discovery_contract_spec.spl (93) > test/01_unit/lib/editor/extension_discovery_contract_spec.spl (92)
test/unit/lib/nogc_async_mut/async_embedded_spec.spl (248) > test/01_unit/lib/nogc_async_mut/async_embedded_spec.spl (4)
test/unit/lib/nogc_async_mut/async_host_spec.spl (380) > test/01_unit/lib/nogc_async_mut/async_host_spec.spl (74)
test/unit/lib/nogc_async_mut/concurrent_spec.spl (231) > test/01_unit/lib/nogc_async_mut/concurrent_spec.spl (227)
test/unit/lib/nogc_async_mut/http_server/static_file_compression_cache_spec.spl (164) > test/01_unit/lib/nogc_async_mut/http_server/static_file_compression_cache_spec.spl (158)
test/unit/lib/nogc_async_mut/http_server/static_file_handler_compression_spec.spl (189) > test/01_unit/lib/nogc_async_mut/http_server/static_file_handler_compression_spec.spl (180)
test/unit/lib/qemu_spec.spl (222) > test/01_unit/lib/qemu_spec.spl (50)
test/unit/lib/skia/canvas_spec.spl (134) > test/01_unit/lib/skia/canvas_spec.spl (123)
test/unit/lib/std/concurrency/concurrency_spec.spl (580) > test/01_unit/lib/std/concurrency/concurrency_spec.spl (574)
test/unit/os/installer/image_builder_artifact_spec.spl (124) > test/01_unit/os/installer/image_builder_artifact_spec.spl (51)
test/unit/os/kernel/memory/pmm_spec.spl (196) > test/01_unit/os/kernel/memory/pmm_spec.spl (186)
test/unit/os/kernel/memory/vmm_vma_spec.spl (303) > test/01_unit/os/kernel/memory/vmm_vma_spec.spl (261)
test/unit/os/proxy/stun_spec.spl (528) > test/01_unit/os/proxy/stun_spec.spl (513)
test/unit/os/tls13/server_accept_spec.spl (810) > test/01_unit/os/tls13/server_accept_spec.spl (751)
test/unit/std/context_spec.spl (110) > test/01_unit/std/context_spec.spl (20)
test/unit/std/exp/artifact_spec.spl (77) > test/01_unit/std/exp/artifact_spec.spl (14)
test/unit/std/exp/config_spec.spl (163) > test/01_unit/std/exp/config_spec.spl (14)
test/unit/std/exp/run_spec.spl (111) > test/01_unit/std/exp/run_spec.spl (15)
test/unit/std/exp/sweep_spec.spl (150) > test/01_unit/std/exp/sweep_spec.spl (17)
test/unit/std/hooks/hook_registry_spec.spl (181) > test/01_unit/std/hooks/hook_registry_spec.spl (26)
test/unit/std/mock_phase4_spec.spl (594) > test/01_unit/std/mock_phase4_spec.spl (591)
test/unit/std/mock_phase5_spec.spl (582) > test/01_unit/std/mock_phase5_spec.spl (579)
test/unit/std/mock_phase7_spec.spl (1162) > test/01_unit/std/mock_phase7_spec.spl (1144)
test/feature/lib/mcp/handler_import_test.spl (32) > test/03_system/feature/lib/mcp/handler_import_test.spl (22)
test/feature/lib/mcp/simple_import_test.spl (39) > test/03_system/feature/lib/mcp/simple_import_test.spl (25)
test/feature/usage/alias_deprecated_spec.spl (596) > test/03_system/feature/usage/alias_deprecated_spec.spl (594)
test/feature/usage/class_invariant_spec.spl (350) > test/03_system/feature/usage/class_invariant_spec.spl (347)
test/feature/usage/hm_type_inference_spec.spl (509) > test/03_system/feature/usage/hm_type_inference_spec.spl (504)
test/feature/usage/pass_variants_spec.spl (165) > test/03_system/feature/usage/pass_variants_spec.spl (153)
test/feature/usage/static_const_declarations_spec.spl (576) > test/03_system/feature/usage/static_const_declarations_spec.spl (540)
test/feature/usage/string_interpolation_spec.spl (197) > test/03_system/feature/usage/string_interpolation_spec.spl (192)
test/feature/usage/trait_forwarding_spec.spl (245) > test/03_system/feature/usage/trait_forwarding_spec.spl (240)
test/feature/web_platform/css/transforms_wpt_spec.spl (131) > test/03_system/feature/web_platform/css/transforms_wpt_spec.spl (125)
test/integration/app/linkers_log_modes_spec.spl (42) > test/02_integration/app/linkers_log_modes_spec.spl (41)
test/integration/app/optimize/optimize_cli_spec.spl (242) > test/02_integration/app/optimize/optimize_cli_spec.spl (120)
test/integration/app/primitive_api_lint_spec.spl (49) > test/02_integration/app/primitive_api_lint_spec.spl (48)
test/integration/examples/platform_library_example_spec.spl (286) > test/02_integration/examples/platform_library_example_spec.spl (283)
test/integration/lib/std/doctest/discovery_spec.spl (91) > test/02_integration/lib/std/doctest/discovery_spec.spl (49)
test/integration/os/port/bootstrap_cross_status_spec.spl (23) > test/02_integration/os/port/bootstrap_cross_status_spec.spl (22)
test/integration/os/port/native_convergence_spec.spl (64) > test/02_integration/os/port/native_convergence_spec.spl (59)
test/system/app/compiler/feature/all_regions_spec.spl (21) > test/03_system/app/compiler/feature/all_regions_spec.spl (20)
test/system/compiler/driver_api_tier_policy_spec.spl (335) > test/03_system/compiler/driver_api_tier_policy_spec.spl (309)
test/system/database/server/db_durability_spec.spl (469) > test/03_system/database/server/db_durability_spec.spl (453)
test/system/database/server/db_server_tier_spec.spl (438) > test/03_system/database/server/db_server_tier_spec.spl (419)
test/system/gui/native_gui_build_spec.spl (344) > test/03_system/gui/native_gui_build_spec.spl (339)
test/system/net_connect_completion_spec.spl (123) > test/03_system/net_connect_completion_spec.spl (120)
test/system/os_crypto_ref_helpers.spl (311) > test/03_system/os_crypto_ref_helpers.spl (6)
test/perf/bench/jit_minimal_test.spl (23) > test/05_perf/bench/jit_minimal_test.spl (11)
test/perf/cli_dispatch_perf_spec.spl (270) > test/05_perf/cli_dispatch_perf_spec.spl (251)
test/perf/ctype/bench_ctype_static_lut.spl (136) > test/05_perf/ctype/bench_ctype_static_lut.spl (134)
test/perf/ctype/global_static_array_smoke.spl (26) > test/05_perf/ctype/global_static_array_smoke.spl (25)
test/perf/web_render_chrome/web_paint_cache_spec.spl (156) > test/05_perf/web_render_chrome/web_paint_cache_spec.spl (155)
```

## Divergent pairs by tree

```
--- div_test_01_unit (843 pairs) ---
DIVERGENT app/branch_coverage_7_spec.spl
DIVERGENT app/cli/cli_migration_spec.spl
DIVERGENT app/cli/cli_os_spec.spl
DIVERGENT app/cli/native_build_arg_source_spec.spl
DIVERGENT app/cli_parser_spec.spl
DIVERGENT app/cli/query_ast_query_integration_spec.spl
DIVERGENT app/cli/query_sem_query_integration_spec.spl
DIVERGENT app/cli/query_visibility_spec.spl
DIVERGENT app/cmm_lsp/cmm_dialog_label_ref_spec.spl
DIVERGENT app/compile/cli_compile_surface_spec.spl
DIVERGENT app/compile/cli_native_build_spec.spl
DIVERGENT app/dap/adapter_unification_spec.spl
DIVERGENT app/dap/breakpoints_spec.spl
DIVERGENT app/dap/dap_spec.spl
DIVERGENT app/dap/debug_adapter_spec.spl
DIVERGENT app/dap/debug_configuration_spec.spl
DIVERGENT app/dap/debug_session_spec.spl
DIVERGENT app/dap/debug_state_spec.spl
DIVERGENT app/dap/interpreter_hooks_spec.spl
DIVERGENT app/dap/protocol_spec.spl
DIVERGENT app/dap/server_hooks_integration_spec.spl
DIVERGENT app/dap/server_spec.spl
DIVERGENT app/diagram/diagram_gen_spec.spl
DIVERGENT app/diagram/filter_spec.spl
DIVERGENT app/doc_coverage/compiler_integration_spec.spl
DIVERGENT app/doc_coverage/group_comment_detection_spec.spl
DIVERGENT app/doc_coverage/inline_comment_coverage_spec.spl
DIVERGENT app/doc_coverage/tag_validator_spec.spl
DIVERGENT app/doc_coverage/threshold_calculator_spec.spl
DIVERGENT app/doc/public_check/statistics_spec.spl
DIVERGENT app/doc/public_check/warnings_spec.spl
DIVERGENT app/duplicate_check/detector_grouping_spec.spl
DIVERGENT app/duplicate_check/semantic_spec.spl
DIVERGENT app/fix/lint_spec.spl
DIVERGENT app/fix/short_grammar_fix_spec.spl
DIVERGENT app/formatter_comprehensive_spec.spl
DIVERGENT app/formatter/formatter_basic_spec.spl
DIVERGENT app/formatter/formatter_comprehensive_spec.spl
DIVERGENT app/formatter/formatter_spec.spl
DIVERGENT app/formatter_spec.spl
DIVERGENT app/interpreter/actor_scheduler_spec.spl
DIVERGENT app/interpreter/lazy_val_spec.spl
DIVERGENT app/interpreter/message_transfer_spec.spl
DIVERGENT app/interpreter/perf_spec.spl
DIVERGENT app/interpreter/symbol_spec.spl
DIVERGENT app/inventory_drift_spec.spl
DIVERGENT app/io/cli_ops_handlers_spec.spl
DIVERGENT app/io/file_shell_exec_spec.spl
DIVERGENT app/io/process_ops_ext_spec.spl
DIVERGENT app/io/timeout_spec.spl
DIVERGENT app/llm_caret/chat_spec.spl
DIVERGENT app/llm_caret/claude_api_spec.spl
DIVERGENT app/llm_caret/claude_cli_spec.spl
DIVERGENT app/llm_caret/config_spec.spl
DIVERGENT app/llm_caret/gemini_cli_spec.spl
DIVERGENT app/llm_caret/openai_api_spec.spl
DIVERGENT app/llm_caret/opencode_cli_spec.spl
DIVERGENT app/llm_caret/provider_spec.spl
DIVERGENT app/llm_caret/server_spec.spl
DIVERGENT app/llm_runtime/vllm_dashboard_live_control_spec.spl
DIVERGENT app/lms/server_spec.spl
DIVERGENT app/lsp/code_action_kind_spec.spl
DIVERGENT app/lsp/helper_functions_spec.spl
DIVERGENT app/lsp/server_capabilities_spec.spl
DIVERGENT app/lsp/symbol_kind_spec.spl
DIVERGENT app/lsp/workspace_edit_spec.spl
DIVERGENT app/mcp/cli_passthrough_spec.spl
DIVERGENT app/mcp_t32/mcp_t32_wsl_wrapper_spec.spl
DIVERGENT app/mcp_unit/assistant_surface_spec.spl
DIVERGENT app/mcp_unit/assistant_task_linking_spec.spl
DIVERGENT app/mcp_unit/command_filter_spec.spl
DIVERGENT app/mcp_unit/coordinator_extended_spec.spl
DIVERGENT app/mcp_unit/crash_prevention_spec.spl
DIVERGENT app/mcp_unit/debug_coordinator_spec.spl
DIVERGENT app/mcp_unit/debug_eval_spec.spl
DIVERGENT app/mcp_unit/editor_spec.spl
DIVERGENT app/mcp_unit/error_handler_edge_cases_spec.spl
DIVERGENT app/mcp_unit/error_handler_spec.spl
DIVERGENT app/mcp_unit/fileio_protection_spec.spl
DIVERGENT app/mcp_unit/logging_basics_spec.spl
DIVERGENT app/mcp_unit/mcp_analysis_tools_spec.spl
DIVERGENT app/mcp_unit/mcp_inventory_alignment_spec.spl
DIVERGENT app/mcp_unit/resources_spec.spl
DIVERGENT app/mcp_unit/server_safe_operations_spec.spl
DIVERGENT app/mcp_unit/session_extended_spec.spl
DIVERGENT app/mcp_unit/session_spec.spl
DIVERGENT app/mcp_unit/simple_mcp_malformed_spec.spl
DIVERGENT app/mcp_unit/tasks_spec.spl
DIVERGENT app/mcp_unit/transport_edge_cases_spec.spl
DIVERGENT app/mcp_unit/transport_error_handling_spec.spl
DIVERGENT app/mcp_unit/transport_tcp_spec.spl
DIVERGENT app/mcp_unit/validation_spec.spl
DIVERGENT app/office/office_suite_spec.spl
DIVERGENT app/package_cli_spec.spl
DIVERGENT app/package/ffi_spec.spl
DIVERGENT app/package/lockfile_spec.spl
DIVERGENT app/package/manifest_spec.spl
DIVERGENT app/package/package_spec.spl
DIVERGENT app/package/semver_mini_spec.spl
DIVERGENT app/project_cli_spec.spl
DIVERGENT app/semihost/reader_spec.spl
DIVERGENT app/simpleos_nvme_serial_check_spec.spl
DIVERGENT app/svllm_pack/main_spec.spl
DIVERGENT app/test_daemon/test_daemon_gui_routing_spec.spl
DIVERGENT app/test_runner_new/container_backend_spec.spl
DIVERGENT app/test_runner_new/test_config_spec.spl
DIVERGENT app/test_runner_new/test_manifest_spec.spl
DIVERGENT app/test_runner_new/test_result_cache_spec.spl
DIVERGENT app/test_runner_new/test_runner_args_ci_spec.spl
DIVERGENT app/test_runner/types_spec.spl
DIVERGENT app/todo/todo_parser_spec.spl
DIVERGENT app/tooling/arg_parsing_spec.spl
DIVERGENT app/tooling/brief_view_spec.spl
DIVERGENT app/tooling/color_utils_spec.spl
DIVERGENT app/tooling/command_dispatch_spec.spl
DIVERGENT app/tooling/compile_commands_spec.spl
DIVERGENT app/tooling/context_generate_spec.spl
DIVERGENT app/tooling/context_pack_spec.spl
DIVERGENT app/tooling/coverage_ffi_spec.spl
DIVERGENT app/tooling/coverage_threshold_spec.spl
DIVERGENT app/tooling/sandbox_spec.spl
DIVERGENT app/tooling/spipe_docgen_scenario_body_spec.spl
DIVERGENT app/tooling/symbol_hash_spec.spl
DIVERGENT app/tooling/test_db_edge_cases_spec.spl
DIVERGENT app/tooling/test_db_types_spec.spl
DIVERGENT app/tooling/test_runner_simple_spec.spl
DIVERGENT app/tooling/test_stats_spec.spl
DIVERGENT app/tooling/todo_parser_spec.spl
DIVERGENT app/tooling/tooling_spec.spl
DIVERGENT app/ui/access_spec.spl
DIVERGENT app/ui/async_web_spec.spl
DIVERGENT app/ui/backend_matrix_spec.spl
DIVERGENT app/ui/browser_static_shell_cache_spec.spl
DIVERGENT app/ui.chromium.devtools/attach_session_spec.spl
DIVERGENT app/ui.chromium/js_audit_spec.spl
DIVERGENT app/ui.chromium/text_metrics_spec.spl
DIVERGENT app/ui/cli_observer_spec.spl
DIVERGENT app/ui/cli_socket_spec.spl
DIVERGENT app/ui.electron/main_spec.spl
DIVERGENT app/ui/event_queue_spec.spl
DIVERGENT app/ui/headless_app_spec.spl
DIVERGENT app/ui/host_wm_runtime_loop_spec.spl
DIVERGENT app/ui/html_render_spec.spl
DIVERGENT app/ui/ipc_protocol_spec.spl
DIVERGENT app/ui/ipc_surface_spec.spl
DIVERGENT app/ui/surface_spec.spl
DIVERGENT app/ui/tauri_backend_spec.spl
DIVERGENT app/ui/tauri_entry_common_envelope_spec.spl
DIVERGENT app/ui.test_api/handler_test.spl
DIVERGENT app/ui/test_api_mount_spec.spl
DIVERGENT app/ui/token_resolution_spec.spl
DIVERGENT app/ui/ui_access_http_spec.spl
DIVERGENT app/ui/ui_access_runtime_spec.spl
DIVERGENT app/ui/ui_access_store_spec.spl
DIVERGENT app/ui/ui_access_vision_spec.spl
DIVERGENT app/ui/web_render_backend_api_spec.spl
DIVERGENT app/ui/web_render_cache_spec.spl
DIVERGENT app/ui/widget_button_checkbox_dropdown_spec.spl
DIVERGENT app/ui/widget_menubar_statusbar_spec.spl
DIVERGENT app/ui/widget_menu_tooltip_spec.spl
DIVERGENT app/ui/widget_modifiers_spec.spl
DIVERGENT app/ui/widget_panel_text_divider_spec.spl
DIVERGENT app/ui/widget_progress_image_tooltip_spec.spl
DIVERGENT app/ui/widget_scroll_textarea_spec.spl
DIVERGENT app/ui/widget_tabs_list_dialog_spec.spl
DIVERGENT app/ui/widget_tree_spec.spl
DIVERGENT app/ui/wm_runtime_bridge_spec.spl
DIVERGENT app/ui/ws_handler_spec.spl
DIVERGENT baremetal/riscv/fpga_boot_linux_spec.spl
DIVERGENT browser_engine/html5lib_tokenizer_spec.spl
DIVERGENT browser_engine/html_tokenizer_spec.spl
DIVERGENT browser_engine/html_tree_builder_spec.spl
DIVERGENT browser_engine/ifc_linebox_spec.spl
DIVERGENT browser_engine/margin_collapse_spec.spl
DIVERGENT browser_engine/net/cookie_store_spec.spl
DIVERGENT browser_engine/net/cors_spec.spl
DIVERGENT browser_engine/script/event_loop_spec.spl
DIVERGENT browser_engine/script/network_api_spec.spl
DIVERGENT browser_engine/script/script_host_spec.spl
DIVERGENT browser_engine/script/simple_script_spec.spl
DIVERGENT browser_engine/table_layout_spec.spl
DIVERGENT browser_engine/text_painter_spec.spl
DIVERGENT browser/script/timer_api_spec.spl
DIVERGENT bugs/dict_type_annotation_spec.spl
DIVERGENT bugs/export_as_runtime_bug_spec.spl
DIVERGENT bugs/parser_const_pointer_spec.spl
DIVERGENT compiler/60.mir_opt/general_patterns_spec.spl
DIVERGENT compiler/async/async_integration_spec.spl
DIVERGENT compiler/async/async_mir_interpreter_spec.spl
DIVERGENT compiler/async/async_state_machine_spec.spl
DIVERGENT compiler/async/poll_generator_spec.spl
DIVERGENT compiler/backend/c_backend_export_spec.spl
DIVERGENT compiler/backend/cranelift_gemm_fusion_spec.spl
DIVERGENT compiler/backend/interpreter_backend_spec.spl
DIVERGENT compiler/backend/layout_scanner_spec.spl
DIVERGENT compiler/backend/linker/archive_parser_spec.spl
DIVERGENT compiler/backend/linker/elf_parser_spec.spl
DIVERGENT compiler/backend/linker/linker_script_spec.spl
DIVERGENT compiler/backend/llvm_bootstrap_accumulator_reset_spec.spl
DIVERGENT compiler/backend/llvm_ir_builder_spec.spl
DIVERGENT compiler/backend/llvm_lib_backend_spec.spl
DIVERGENT compiler/backend/native_backend_spec.spl
DIVERGENT compiler/backend/native/encode_riscv32_spec.spl
DIVERGENT compiler/backend/native/encode_riscv64_spec.spl
DIVERGENT compiler/backend/native/isel_riscv32_spec.spl
DIVERGENT compiler/backend/native/isel_riscv64_spec.spl
DIVERGENT compiler/backend/native/isel_x86_64_spec.spl
DIVERGENT compiler/backend/native_layout_spec.spl
DIVERGENT compiler/backend/riscv_target_spec.spl
DIVERGENT compiler/backend/runtime_compiler_spec.spl
DIVERGENT compiler/backend/spipe_system_test_spec.spl
DIVERGENT compiler/backend/target_matrix_spec.spl
DIVERGENT compiler/backend/vhdl_abi_spec.spl
DIVERGENT compiler/backend/vhdl_backend_spec.spl
DIVERGENT compiler/backend/vhdl_testbench_spec.spl
DIVERGENT compiler/blocks/builder_api_basic_spec.spl
DIVERGENT compiler/blocks/builder_default_parser_spec.spl
DIVERGENT compiler/blocks/easy_api_basic_spec.spl
DIVERGENT compiler/blocks/testing_framework_spec.spl
DIVERGENT compiler/blocks/utils_basic_spec.spl
DIVERGENT compiler/borrow/borrow_check_spec.spl
DIVERGENT compiler/cache/compile_options_hash_spec.spl
DIVERGENT compiler/codegen/baremetal_cross_module_val_spec.spl
DIVERGENT compiler/codegen/baremetal_method_dispatch_spec.spl
DIVERGENT compiler/codegen/gpu_portable_compute_spec.spl
DIVERGENT compiler/codegen/method_dispatch_uncovered_gaps_spec.spl
DIVERGENT compiler/common/attributes_spec.spl
DIVERGENT compiler/config/dict_get_optional_spec.spl
DIVERGENT compiler_core/annotation_intrinsics_spec.spl
DIVERGENT compiler_core/ast_clone_spec.spl
DIVERGENT compiler_core/bidir_type_check_spec.spl
DIVERGENT compiler_core/bind_stmt_spec.spl
DIVERGENT compiler_core/branch_coverage_12_spec.spl
DIVERGENT compiler_core/branch_coverage_23_spec.spl
DIVERGENT compiler_core/ce_block_spec.spl
DIVERGENT compiler_core/entity/entity_span_spec.spl
DIVERGENT compiler_core/exhaustiveness_spec.spl
DIVERGENT compiler_core/file_class_introspection_spec.spl
DIVERGENT compiler_core/generic_syntax_spec.spl
DIVERGENT compiler_core/ignored_return_warning_spec.spl
DIVERGENT compiler_core/interpreter/env_spec.spl
DIVERGENT compiler_core/interpreter/eval_spec.spl
DIVERGENT compiler_core/interpreter/intensive_spec.spl
DIVERGENT compiler_core/interpreter/jit_spec.spl
DIVERGENT compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl
DIVERGENT compiler_core/interpreter/ops_spec.spl
DIVERGENT compiler_core/interpreter/value_spec.spl
DIVERGENT compiler_core/keyof_spec.spl
DIVERGENT compiler_core/keyof_token_spec.spl
DIVERGENT compiler_core/lang_basics_spec.spl
DIVERGENT compiler_core/mir_spec.spl
DIVERGENT compiler_core/mixin_expr_spec.spl
DIVERGENT compiler_core/must_use_spec.spl
DIVERGENT compiler_core/pragma_msg_spec.spl
DIVERGENT compiler_core/preprocess_conditionals_spec.spl
DIVERGENT compiler_core/receive_spec.spl
DIVERGENT compiler_core/tmp_test_spec.spl
DIVERGENT compiler_core/tokens_spec.spl
DIVERGENT compiler_core/traits_compiles_spec.spl
DIVERGENT compiler_core/traits_extended_spec.spl
DIVERGENT compiler_core/traits_module_spec.spl
DIVERGENT compiler_core/traits_spec.spl
DIVERGENT compiler_core/types_spec.spl
DIVERGENT compiler_core/type_subst_spec.spl
DIVERGENT compiler/coverage/branch_coverage_10_spec.spl
DIVERGENT compiler/coverage/branch_coverage_11_spec.spl
DIVERGENT compiler/coverage/branch_coverage_12_spec.spl
DIVERGENT compiler/coverage/branch_coverage_13_spec.spl
DIVERGENT compiler/coverage/branch_coverage_14_spec.spl
DIVERGENT compiler/coverage/branch_coverage_15_spec.spl
DIVERGENT compiler/coverage/branch_coverage_16_spec.spl
DIVERGENT compiler/coverage/branch_coverage_18_spec.spl
DIVERGENT compiler/coverage/branch_coverage_19_spec.spl
DIVERGENT compiler/coverage/branch_coverage_1_spec.spl
DIVERGENT compiler/coverage/branch_coverage_20_spec.spl
DIVERGENT compiler/coverage/branch_coverage_21_spec.spl
DIVERGENT compiler/coverage/branch_coverage_22_spec.spl
DIVERGENT compiler/coverage/branch_coverage_23_spec.spl
DIVERGENT compiler/coverage/branch_coverage_24_spec.spl
DIVERGENT compiler/coverage/branch_coverage_25_spec.spl
DIVERGENT compiler/coverage/branch_coverage_2_spec.spl
DIVERGENT compiler/coverage/branch_coverage_3_spec.spl
DIVERGENT compiler/coverage/branch_coverage_4_spec.spl
DIVERGENT compiler/coverage/branch_coverage_5_spec.spl
DIVERGENT compiler/coverage/branch_coverage_6_spec.spl
DIVERGENT compiler/coverage/branch_coverage_7_spec.spl
DIVERGENT compiler/coverage/branch_coverage_8_spec.spl
DIVERGENT compiler/coverage/branch_coverage_9_spec.spl
DIVERGENT compiler/custom_blocks_easy_api_spec.spl
DIVERGENT compiler/driver/main_opt_level_cli_spec.spl
DIVERGENT compiler/frontend/aop_log_policy_spec.spl
DIVERGENT compiler/frontend/parser_spec.spl
DIVERGENT compiler/frontend/required_comment_parse_spec.spl
DIVERGENT compiler/hir/domain_block_hir_lowering_spec.spl
DIVERGENT compiler/hir/hir_stage4_field_inference_spec.spl
DIVERGENT compiler/hir/module_filename_populated_spec.spl
DIVERGENT compiler/hir/resolve_import_symbols_spec.spl
DIVERGENT compiler/interpreter/load_session_cache_spec.spl
DIVERGENT compiler/interpreter/mir_ssa_phi_intrinsic_spec.spl
DIVERGENT compiler/interpreter/self_field_assign_spec.spl
DIVERGENT compiler/interpreter/smf_source_spec.spl
DIVERGENT compiler/lexer/lexer_comprehensive_spec.spl
DIVERGENT compiler/lexer/lexer_import_debug_spec.spl
DIVERGENT compiler/lexer/lexer_minimal_test_spec.spl
DIVERGENT compiler/lexer/lexer_new_spec.spl
DIVERGENT compiler/lexer/lexer_spec.spl
DIVERGENT compiler/lexer/source_position_spec.spl
DIVERGENT compiler/linker/lib_smf_spec.spl
DIVERGENT compiler/linker/lib_smf_writer_spec.spl
DIVERGENT compiler/linker/native_link_hardening_spec.spl
DIVERGENT compiler/linker/platform_defaults_spec.spl
DIVERGENT compiler/linker/smf_driver_manifest_section_spec.spl
DIVERGENT compiler/lint/required_comment_cli_spec.spl
DIVERGENT compiler/lint/riscv_rtl_debuggability_spec.spl
DIVERGENT compiler/lint/stub_impl_spec.spl
DIVERGENT compiler/lint/wide_public_spec.spl
DIVERGENT compiler/loader/loader_shared_core_spec.spl
DIVERGENT compiler/loader/metadata_symbols_spec.spl
DIVERGENT compiler/loader/module_loader_relocation_spec.spl
DIVERGENT compiler/loader/runtime_surface_spec.spl
DIVERGENT compiler/mdsoc/pipeline_integration_spec.spl
DIVERGENT compiler/mir/aop_injection_spec.spl
DIVERGENT compiler/mir/mir_exported_types_spec.spl
DIVERGENT compiler/mir/mir_lowering_new_spec.spl
DIVERGENT compiler/mir/mir_pattern_idiom_benchmark_spec.spl
DIVERGENT compiler/mir_opt/cipher/opt_remark_spec.spl
DIVERGENT compiler/mir_opt/cipher/pattern_dispatch_spec.spl
DIVERGENT compiler/mir_opt/cipher/target_opt_context_spec.spl
DIVERGENT compiler/mir_opt/collection_opt_spec.spl
DIVERGENT compiler/mir_opt/constant_folding_spec.spl
DIVERGENT compiler/mir_opt/inlining_spec.spl
DIVERGENT compiler/mir_opt/predicate_promote_spec.spl
DIVERGENT compiler/mir_opt/strength_reduction_spec.spl
DIVERGENT compiler/mir_opt/var_reassign_analysis_spec.spl
DIVERGENT compiler/mir/synthetic_driver_registration_spec.spl
DIVERGENT compiler/module_resolver/type_domain_resolver_spec.spl
DIVERGENT compiler/mono/monomorphize_integration_spec.spl
DIVERGENT compiler/native/build_native_min_spec.spl
DIVERGENT compiler/native/x86_64_simd_spec.spl
DIVERGENT compiler/packed_struct_bitfield_spec.spl
DIVERGENT compiler/parser/bitfield_pure_simple_spec.spl
DIVERGENT compiler/parser/dangerous_comment_grammar_spec.spl
DIVERGENT compiler/parser/flat_ast_pub_decl_spec.spl
DIVERGENT compiler/parser/match_empty_array_bug_spec.spl
DIVERGENT compiler/parser/paren_call_block_spec.spl
DIVERGENT compiler/parser/parser_attribute_spec.spl
DIVERGENT compiler/parser/pub_enum_with_attribute_spec.spl
DIVERGENT compiler/parser/treesitter_highlights_spec.spl
DIVERGENT compiler/parser/treesitter_visibility_spec.spl
DIVERGENT compiler/parser/where_clause_spec.spl
DIVERGENT compiler/r2_lang_probe_spec.spl
DIVERGENT compiler/semantics/alloc_checker_spec.spl
DIVERGENT compiler/semantics/lint/lint_cache_spec.spl
DIVERGENT compiler/semantics/lint/required_comment_lint_spec.spl
DIVERGENT compiler/semantics/preprocessor_when_cfg_spec.spl
DIVERGENT compiler/semantics/uncovered_branches_spec.spl
DIVERGENT compiler_shared/diagnostics/diagnostic_spec.spl
DIVERGENT compiler_shared/diagnostics/label_spec.spl
DIVERGENT compiler_shared/diagnostics/severity_spec.spl
DIVERGENT compiler_shared/diagnostics/span_spec.spl
DIVERGENT compiler/shb/shb_cache_spec.spl
DIVERGENT compiler/shb/shb_roundtrip_spec.spl
DIVERGENT compiler/target_spec_spec.spl
DIVERGENT compiler/tools/api_surface_spec.spl
DIVERGENT compiler/tools/duplicate_check_debug_spec.spl
DIVERGENT compiler/type_inference/dim_constraints_spec.spl
DIVERGENT compiler/types/layout_verification_spec.spl
DIVERGENT compiler/types/platform_layout_attribute_spec.spl
DIVERGENT compiler/types/runtime_layout_verification_spec.spl
DIVERGENT compiler/u32_array_index_shr_spec.spl
DIVERGENT compiler/vhdl/hardware_spawn_lower_spec.spl
DIVERGENT core/parser_ce_keyword_identifier_spec.spl
DIVERGENT doc/feature_requests_spec.spl
DIVERGENT doctest/parser_spec.spl
DIVERGENT fs_driver/error_test.spl
DIVERGENT fs_driver/extension_test.spl
DIVERGENT fs_driver/instance_test.spl
DIVERGENT fs_driver/mount_table_resolve_test.spl
DIVERGENT gpu/graphics_3d_session_managed_backend_spec.spl
DIVERGENT hal/hal_traits_spec.spl
DIVERGENT hardware/fpga_linux/check_riscv_rtl_linux_smoke_spec.spl
DIVERGENT hardware/rv32i_rtl/rvfi_spec.spl
DIVERGENT jit/jit_riscv_hotspot_opt_spec.spl
DIVERGENT lib/alloc/mimalloc_secure_spec.spl
DIVERGENT lib/alloc/mimalloc_tls_spec.spl
DIVERGENT lib/async/async_basics_spec.spl
DIVERGENT lib/bitwise_byte_helpers_spec.spl
DIVERGENT lib/branch_coverage_24_spec.spl
DIVERGENT lib/branch_coverage_3_spec.spl
DIVERGENT lib/cc/property_tree_spec.spl
DIVERGENT lib/cli_output/log_writer_spec.spl
DIVERGENT lib/cli_output/progress_spec.spl
DIVERGENT lib/cli_output/summary_spec.spl
DIVERGENT lib/common/array_coverage_spec.spl
DIVERGENT lib/common/auto_comprehensive_10_spec.spl
DIVERGENT lib/common/auto_comprehensive_13_spec.spl
DIVERGENT lib/common/auto_comprehensive_24_spec.spl
DIVERGENT lib/common/base_encoding/base64/base64_spec.spl
DIVERGENT lib/common/collections_spec.spl
DIVERGENT lib/common/color_utils_rgb_hsl_spec.spl
DIVERGENT lib/common/compatibility_spec.spl
DIVERGENT lib/common/compress_facade_harness_spec.spl
DIVERGENT lib/common/compress_framework_spec.spl
DIVERGENT lib/common/compress/gzip_spec.spl
DIVERGENT lib/common/compress/lz4_spec.spl
DIVERGENT lib/common/compress/snappy_spec.spl
DIVERGENT lib/common/compress_utilities_spec.spl
DIVERGENT lib/common/condition_spec.spl
DIVERGENT lib/common/context_spec.spl
DIVERGENT lib/common/contracts/new_contracts_spec.spl
DIVERGENT lib/common/crypto/hkdf_sha1_quick_spec.spl
DIVERGENT lib/common/crypto/lshr2_debug_spec.spl
DIVERGENT lib/common/crypto/lshr3_debug_spec.spl
DIVERGENT lib/common/crypto/sha1_spec.spl
DIVERGENT lib/common/crypto/sha256_simd_parity_spec.spl
DIVERGENT lib/common/diagnostics/i18n_context_spec.spl
DIVERGENT lib/common/diagnostics/json_formatter_spec.spl
DIVERGENT lib/common/diagnostics/simple_formatter_spec.spl
DIVERGENT lib/common/diagnostics/text_formatter_spec.spl
DIVERGENT lib/common/ds_utils_stack_queue_spec.spl
DIVERGENT lib/common/encoding/base58_spec.spl
DIVERGENT lib/common/encoding/utf16_spec.spl
DIVERGENT lib/common/encoding/utf8_spec.spl
DIVERGENT lib/common/error_core_spec.spl
DIVERGENT lib/common/error_format_spec.spl
DIVERGENT lib/common/error_spec.spl
DIVERGENT lib/common/exp/artifact_spec.spl
DIVERGENT lib/common/exp/config_spec.spl
DIVERGENT lib/common/export_star_spec.spl
DIVERGENT lib/common/exp/run_spec.spl
DIVERGENT lib/common/exp/storage_spec.spl
DIVERGENT lib/common/exp/sweep_spec.spl
DIVERGENT lib/common/fault_detection_enhanced_spec.spl
DIVERGENT lib/common/feature_validation/testing_framework_spec.spl
DIVERGENT lib/common/format_spec.spl
DIVERGENT lib/common/fuzz_spec.spl
DIVERGENT lib/common/helpers_spec.spl
DIVERGENT lib/common/hooks/hook_registry_spec.spl
DIVERGENT lib/common/hpack/huffman_h2_spec.spl
DIVERGENT lib/common/hpack/string_codec_spec.spl
DIVERGENT lib/common/js_async_fetch_spec.spl
DIVERGENT lib/common/js_jit_optimizer_spec.spl
DIVERGENT lib/common/json_logic_spec.spl
DIVERGENT lib/common/js_runtime_host_property_spec.spl
DIVERGENT lib/common/js_runtime_node_fast_path_spec.spl
DIVERGENT lib/common/jwt_spec.spl
DIVERGENT lib/common/let_memoization_spec.spl
DIVERGENT lib/common/llm/output_gate_spec.spl
DIVERGENT lib/common/log_export_spec.spl
DIVERGENT lib/common/lz4_spec.spl
DIVERGENT lib/common/mathjax_spec.spl
DIVERGENT lib/common/math_repr_error_spec.spl
DIVERGENT lib/common/math_repr_plain_coverage_spec.spl
DIVERGENT lib/common/math_repr_spec.spl
DIVERGENT lib/common/mock_phase3_spec.spl
DIVERGENT lib/common/mock_phase4_spec.spl
DIVERGENT lib/common/mock_phase5_spec.spl
DIVERGENT lib/common/mock_phase6_spec.spl
DIVERGENT lib/common/mock_phase7_spec.spl
DIVERGENT lib/common/mock_spec.spl
DIVERGENT lib/common/mock_verification_spec.spl
DIVERGENT lib/common/module_import_spec.spl
DIVERGENT lib/common/newline_constants_spec.spl
DIVERGENT lib/common/option_spec.spl
DIVERGENT lib/common/parser_spec.spl
DIVERGENT lib/common/parsers_sdn_coverage_spec.spl
DIVERGENT lib/common/pending_on_spec.spl
DIVERGENT lib/common/perf_optimization_spec.spl
DIVERGENT lib/common/png_decode_spec.spl
DIVERGENT lib/common/pure/autograd_advanced_spec.spl
DIVERGENT lib/common/pure/autograd_extended_spec.spl
DIVERGENT lib/common/pure/autograd_spec.spl
DIVERGENT lib/common/pure/data_loader_spec.spl
DIVERGENT lib/common/pure/data_spec.spl
DIVERGENT lib/common/pure/metrics_spec.spl
DIVERGENT lib/common/pure/nn_extended_spec.spl
DIVERGENT lib/common/pure/nn/functional_spec.spl
DIVERGENT lib/common/pure/nn/init_spec.spl
DIVERGENT lib/common/pure/nn/loss_spec.spl
DIVERGENT lib/common/pure/nn/norm_spec.spl
DIVERGENT lib/common/pure/nn/pooling_spec.spl
DIVERGENT lib/common/pure/nn_spec.spl
DIVERGENT lib/common/pure/optim/scheduler_spec.spl
DIVERGENT lib/common/pure/pure_parser_load_spec.spl
DIVERGENT lib/common/pure/pure_parser_phase1_2_spec.spl
DIVERGENT lib/common/pure/pure_parser_phase1_spec.spl
DIVERGENT lib/common/pure/tensor_advanced_spec.spl
DIVERGENT lib/common/pure/tensor_f64_ops_extended_spec.spl
DIVERGENT lib/common/pure/tensor_ops_spec.spl
DIVERGENT lib/common/pure/tensor_spec.spl
DIVERGENT lib/common/pure/training_extended_spec.spl
DIVERGENT lib/common/pure/training_spec.spl
DIVERGENT lib/common/pure/utils_spec.spl
DIVERGENT lib/common/regex_char_utils_coverage_spec.spl
DIVERGENT lib/common/result_ce_spec.spl
DIVERGENT lib/common/roundtrip_spec.spl
DIVERGENT lib/common/sdn_coverage_spec.spl
DIVERGENT lib/common/set_utils_operations_spec.spl
DIVERGENT lib/common/spec_framework_spec.spl
DIVERGENT lib/common/string_core_ops_spec.spl
DIVERGENT lib/common/string_core_spec.spl
DIVERGENT lib/common/string_spec.spl
DIVERGENT lib/common/test_meta_spec.spl
DIVERGENT lib/common/text_layout/font_renderer_spec.spl
DIVERGENT lib/common/time_utils/time_utils_spec.spl
DIVERGENT lib/common/torch/dyn_sffi_ops_readiness_spec.spl
DIVERGENT lib/common/torch/torch_device_placement_status_spec.spl
DIVERGENT lib/common/torch/torch_training_seed_status_spec.spl
DIVERGENT lib/common/traits_spec.spl
DIVERGENT lib/common/traits_wired_spec.spl
DIVERGENT lib/common/ui/html_window_spec.spl
DIVERGENT lib/common/ui/theme_package_spec.spl
DIVERGENT lib/common/ui/wasm_hello_gui_spec.spl
DIVERGENT lib/common/ui/web_render_api_spec.spl
DIVERGENT lib/common/ui/window_scene_spec.spl
DIVERGENT lib/common/ui/wm_runtime_dispatch_spec.spl
DIVERGENT lib/common/unicode_math_spec.spl
DIVERGENT lib/common/units/world_units_spec.spl
DIVERGENT lib/common/value_spec.spl
DIVERGENT lib/common/web/browser_session_async_spec.spl
DIVERGENT lib/common/web/browser_session_fetch_wasm_chain_spec.spl
DIVERGENT lib/common/web/browser_session_node_host_gc_async_spec.spl
DIVERGENT lib/common/web/browser_session_node_host_spec.spl
DIVERGENT lib/common/web/browser_session_spec.spl
DIVERGENT lib/common/web/browser_session_storage_spec.spl
DIVERGENT lib/common/web/browser_session_wasm_host_spec.spl
DIVERGENT lib/common/web/simple_browser_page_spec.spl
DIVERGENT lib/common/window_protocol/input_translator_spec.spl
DIVERGENT lib/common/win_fs/window_record_spec.spl
DIVERGENT lib/common/xz_lzma2_periodic_encode_spec.spl
DIVERGENT lib/common/zstd_frame_variants_spec.spl
DIVERGENT lib/common/zstd_fse_weights_spec.spl
DIVERGENT lib/common/zstd_sequence_fse_execution_spec.spl
DIVERGENT lib/common/zstd_sequence_rle_spec.spl
DIVERGENT lib/crypto/aes128_ccm_rfc3610_kat_spec.spl
DIVERGENT lib/crypto/aes256_gcm_nist_vectors_spec.spl
DIVERGENT lib/crypto/aes256_simd_round_spec.spl
DIVERGENT lib/crypto/aes_ctr_nist_spec.spl
DIVERGENT lib/crypto/aes_gcm_siv_rfc8452_kat_spec.spl
DIVERGENT lib/crypto/blake2s_spec.spl
DIVERGENT lib/crypto/curve25519_rfc7748_spec.spl
DIVERGENT lib/crypto/ed25519_rfc8032_spec.spl
DIVERGENT lib/crypto/p256_ct_property_spec.spl
DIVERGENT lib/crypto/rsa_pss_sha256_kat_spec.spl
DIVERGENT lib/crypto/rsa_pss_sha256_roundtrip_slow_spec.spl
DIVERGENT lib/crypto/sha1_x4_spec.spl
DIVERGENT lib/crypto/sha256_x4_spec.spl
DIVERGENT lib/crypto/slh_dsa_128s_spec.spl
DIVERGENT lib/crypto/slh_dsa_192s_256s_spec.spl
DIVERGENT lib/daemon_sdk/daemon_sdk_client_spec.spl
DIVERGENT lib/database/core_interner_table_spec.spl
DIVERGENT lib/database/database_atomic_spec.spl
DIVERGENT lib/database/database_e2e_spec.spl
DIVERGENT lib/database/database_feature_spec.spl
DIVERGENT lib/database/database_test_extended_spec.spl
DIVERGENT lib/database/feature_utils_extract_spec.spl
DIVERGENT lib/database/sql/sql_interceptor_spec.spl
DIVERGENT lib/database/sql/sql_repository_spec.spl
DIVERGENT lib/database/sql/sql_types_spec.spl
DIVERGENT lib/debug/remote/session_model_spec.spl
DIVERGENT lib/dependency_boundary_spec.spl
DIVERGENT lib/diagnostics/i18n_context_spec.spl
DIVERGENT lib/diagnostics/json_formatter_spec.spl
DIVERGENT lib/diagnostics/simple_formatter_spec.spl
DIVERGENT lib/driver/driver_manifest_test.spl
DIVERGENT lib/driver/null_block_driver_test.spl
DIVERGENT lib/ecs/ecs_spec.spl
DIVERGENT lib/editor/editor_launch_contract_spec.spl
DIVERGENT lib/editor/extension_discovery_contract_spec.spl
DIVERGENT lib/editor/host_simpleos_surface_contract_spec.spl
DIVERGENT lib/editor/md_editing_spec.spl
DIVERGENT lib/editor/unified/unified_backend_spec.spl
DIVERGENT lib/engine/atlas_builder_spec.spl
DIVERGENT lib/engine/font_ffi_spec.spl
DIVERGENT lib/engine/object_pool_spec.spl
DIVERGENT lib/engine/physics/physics2/backend_equiv_spec.spl
DIVERGENT lib/engine/physics/physics2/raycast_spec.spl
DIVERGENT lib/engine/physics/physics2/world2d_spec.spl
DIVERGENT lib/engine/physics/physics2/world3d_spec.spl
DIVERGENT lib/engine/vector_spec.spl
DIVERGENT lib/fs_driver/fat32_core_lfn_spec.spl
DIVERGENT lib/gc_async_immut/facade_resolution_spec.spl
DIVERGENT lib/gc_async_immut/native_combinators_spec.spl
DIVERGENT lib/gc_async_mut/database/vector/database_vector_facade_spec.spl
DIVERGENT lib/gc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl
DIVERGENT lib/gc_async_mut/db/dbfs_engine/dbfs_engine_facade_spec.spl
DIVERGENT lib/gc_async_mut/db/dbfs_engine/dbfs_schema_facade_spec.spl
DIVERGENT lib/gc_async_mut/engine/llm/engine_llm_facade_spec.spl
DIVERGENT lib/gc_async_mut/gpu/browser_engine/browser_renderer_dom_events_spec.spl
DIVERGENT lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl
DIVERGENT lib/gc_async_mut/gpu/browser_engine/paint_image_scene_spec.spl
DIVERGENT lib/gc_async_mut/gpu/browser_engine/selector_matcher_spec.spl
DIVERGENT lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer_spec.spl
DIVERGENT lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl
DIVERGENT lib/gc_async_mut/gpu/browser_engine/web_renderer_backend_parity_spec.spl
DIVERGENT lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl
DIVERGENT lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl
DIVERGENT lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl
DIVERGENT lib/gc_async_mut/mcp_sdk/core/core_facade_spec.spl
DIVERGENT lib/gc_async_mut/src/tooling/tooling_facade_spec.spl
DIVERGENT lib/gc_async_mut/svllm/model_executor/model_loader/manifest_spec.spl
DIVERGENT lib/gc_async_mut/svllm/model_executor/model_loader/safetensors_spec.spl
DIVERGENT lib/gc_async_mut/text_layout/text_layout_facade_spec.spl
DIVERGENT lib/gc_async_mut/udp_utils_facade_spec.spl
DIVERGENT lib/gc_async_mut/web_ui/web_ui_facade_spec.spl
DIVERGENT lib/gc_sync_immut/facade_resolution_spec.spl
DIVERGENT lib/gc_sync_immut/native_combinators_spec.spl
DIVERGENT lib/gpu/engine2d/backend_software_primitives_spec.spl
DIVERGENT lib/gpu/engine2d/backend_software_simd_spec.spl
DIVERGENT lib/gpu/engine2d/engine_platform_spec.spl
DIVERGENT lib/gpu/engine2d/ffi_opencl_spec.spl
DIVERGENT lib/gpu/engine2d/ffi_rocm_spec.spl
DIVERGENT lib/gpu/engine2d/generated_kernel_dispatch_spec.spl
DIVERGENT lib/gpu/engine2d/opencl_session_contract_spec.spl
DIVERGENT lib/gpu/engine2d/rendering_opt_provider_spec.spl
DIVERGENT lib/gpu/engine2d/rocm_session_contract_spec.spl
DIVERGENT lib/gpu/engine2d/simd_kernels_spec.spl
DIVERGENT lib/hal/hal_types_spec.spl
DIVERGENT lib/hardware/fpga_linux/soc_vhdl_gen_rv64_spec.spl
DIVERGENT lib/hardware/rv64gc_rtl/core64_integration_spec.spl
DIVERGENT lib/http/h3/h3_frame_round_trip_spec.spl
DIVERGENT lib/http_server/csrf_spec.spl
DIVERGENT lib/lms/server_spec.spl
DIVERGENT lib/nogc_async_mut/async_embedded_spec.spl
DIVERGENT lib/nogc_async_mut/async_host_mt_spec.spl
DIVERGENT lib/nogc_async_mut/async_host_spec.spl
DIVERGENT lib/nogc_async_mut/concurrent_providers_spec.spl
DIVERGENT lib/nogc_async_mut/concurrent_spec.spl
DIVERGENT lib/nogc_async_mut/concurrent_wrappers_spec.spl
DIVERGENT lib/nogc_async_mut/database/vector/database_vector_facade_spec.spl
DIVERGENT lib/nogc_async_mut/db/dbfs_engine/dbfs_checkpoint_attr_facade_spec.spl
DIVERGENT lib/nogc_async_mut/db/dbfs_engine/dbfs_engine_facade_spec.spl
DIVERGENT lib/nogc_async_mut/engine/llm/engine_llm_facade_spec.spl
DIVERGENT lib/nogc_async_mut/game3d/game_loop_spec.spl
DIVERGENT lib/nogc_async_mut/generator_spec.spl
DIVERGENT lib/nogc_async_mut/gen_event_spec.spl
DIVERGENT lib/nogc_async_mut/gen_server_spec.spl
DIVERGENT lib/nogc_async_mut/gen_statem_spec.spl
DIVERGENT lib/nogc_async_mut/gpu/dxvk_spec.spl
DIVERGENT lib/nogc_async_mut/gpu/dxvk_vkd3d_dispatch_spec.spl
DIVERGENT lib/nogc_async_mut/gpu/vulkan_icd_sffi_spec.spl
DIVERGENT lib/nogc_async_mut/host_future_intensive_spec.spl
DIVERGENT lib/nogc_async_mut/http/http_hardening_spec.spl
DIVERGENT lib/nogc_async_mut/http_server/protocol_handler_spec.spl
DIVERGENT lib/nogc_async_mut/http_server/static_compression_cache_spec.spl
DIVERGENT lib/nogc_async_mut/http_server/static_file_compression_cache_spec.spl
DIVERGENT lib/nogc_async_mut/http_server/static_file_handler_compression_spec.spl
DIVERGENT lib/nogc_async_mut/io/async_buffer_spec.spl
DIVERGENT lib/nogc_async_mut/mcp/dispatch_spec.spl
DIVERGENT lib/nogc_async_mut/mcp_sdk/core/core_facade_spec.spl
DIVERGENT lib/nogc_async_mut/ndarray_view_bounds_spec.spl
DIVERGENT lib/nogc_async_mut_noalloc/async/poll_spec.spl
DIVERGENT lib/nogc_async_mut_noalloc/async/scheduler_spec.spl
DIVERGENT lib/nogc_async_mut_noalloc/collections/fixed_stack_spec.spl
DIVERGENT lib/nogc_async_mut_noalloc/collections/linked_list_spec.spl
DIVERGENT lib/nogc_async_mut_noalloc/collections/ring_buffer_spec.spl
DIVERGENT lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl
DIVERGENT lib/nogc_async_mut_noalloc/qemu_spec.spl
DIVERGENT lib/nogc_async_mut/play/cdp/play_cdp_facade_spec.spl
DIVERGENT lib/nogc_async_mut/promise_intensive_spec.spl
DIVERGENT lib/nogc_async_mut/src/tooling/tooling_facade_spec.spl
DIVERGENT lib/nogc_async_mut/test_runner/sdoctest/sdoctest_facade_spec.spl
DIVERGENT lib/nogc_async_mut/text_layout/text_layout_facade_spec.spl
DIVERGENT lib/nogc_async_mut/thread_pool_spec.spl
DIVERGENT lib/nogc_async_mut/thread_safe_queue_spec.spl
DIVERGENT lib/nogc_async_mut/thread_sffi_spec.spl
DIVERGENT lib/nogc_async_mut/tls/ech_spec.spl
DIVERGENT lib/nogc_async_mut/udp_utils_facade_spec.spl
DIVERGENT lib/nogc_async_mut/web_framework/web_framework_facade_spec.spl
DIVERGENT lib/nogc_async_mut/web_ui/web_ui_facade_spec.spl
DIVERGENT lib/nogc_async_mut/wm/compositor_spec.spl
DIVERGENT lib/nogc_async_mut/wm/input_spec.spl
DIVERGENT lib/nogc_sync_mut/compression/zstd/fse_spec.spl
DIVERGENT lib/nogc_sync_mut/compression/zstd/zstd_spec.spl
DIVERGENT lib/nogc_sync_mut/engine/render/backend3d_spec.spl
DIVERGENT lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl
DIVERGENT lib/nogc_sync_mut/engine/render/gpu_mesh3d_spec.spl
DIVERGENT lib/nogc_sync_mut/engine/render/texture3d_spec.spl
DIVERGENT lib/nogc_sync_mut/engine/render/vulkan_backend3d_spec.spl
DIVERGENT lib/nogc_sync_mut/engine/render/webgpu_backend3d_spec.spl
DIVERGENT lib/nogc_sync_mut/hashset_probe_spec.spl
DIVERGENT lib/nogc_sync_mut/http/auth/digest_spec.spl
DIVERGENT lib/play/session_store_spec.spl
DIVERGENT lib/pure/autograd_spec.spl
DIVERGENT lib/pure/data_spec.spl
DIVERGENT lib/pure/metrics_spec.spl
DIVERGENT lib/pure_parser_load_spec.spl
DIVERGENT lib/pure_parser_phase1_2_spec.spl
DIVERGENT lib/pure_parser_phase1_spec.spl
DIVERGENT lib/pure/tensor_advanced_spec.spl
DIVERGENT lib/pure/tensor_f64_ops_extended_spec.spl
DIVERGENT lib/pure/tensor_ops_spec.spl
DIVERGENT lib/pure/tensor_spec.spl
DIVERGENT lib/pure/utils_spec.spl
DIVERGENT lib/qemu_spec.spl
DIVERGENT lib/sanitizer/sanitizer_spec.spl
DIVERGENT lib/security/security_support_spec.spl
DIVERGENT lib/skia/canvas_spec.spl
DIVERGENT lib/skia/glyph_spec.spl
DIVERGENT lib/skia/ot_parser_spec.spl
DIVERGENT lib/skia/shaper_spec.spl
DIVERGENT lib/std/common/text_helpers_spec.spl
DIVERGENT lib/std/concurrency/concurrency_spec.spl
DIVERGENT lib/std/concurrency/promise_spec.spl
DIVERGENT lib/std/file/file_io_spec.spl
DIVERGENT lib/std/ml/tracking/run_spec.spl
DIVERGENT lib/std/shell/file_system_spec.spl
DIVERGENT lib/std/time_spec.spl
DIVERGENT lib/text/utf8_validation_spec.spl
DIVERGENT lib/viz/damage_spec.spl
DIVERGENT memleak/c_runtime_leak_spec.spl
DIVERGENT os/apps/browser_demo_launcher_lifecycle_spec.spl
DIVERGENT os/apps/sshd/sshd_spec.spl
DIVERGENT os/apps/sshd/ssh_kex_hostkey_matrix_spec.spl
DIVERGENT os/apps/sshd/ssh_kex_rsa_contract_spec.spl
DIVERGENT os/apps/sshd/ssh_packet_spec.spl
DIVERGENT os/apps/sshd/ssh_transport_spec.spl
DIVERGENT os/compositor/compositor_spec.spl
DIVERGENT os/compositor/engine2d_glass_spec.spl
DIVERGENT os/compositor/gpu_glass_spec.spl
DIVERGENT os/compositor/host_compositor_entry_spec.spl
DIVERGENT os/compositor/hosted_backend_sdl2_spec.spl
DIVERGENT os/compositor/hosted_backend_win32_spec.spl
DIVERGENT os/compositor/layout_manager_spec.spl
DIVERGENT os/compositor/qemu_capture_ppm_spec.spl
DIVERGENT os/compositor/simpleos_gui_shared_wm_adapter_spec.spl
DIVERGENT os/compositor/wm_action_applier_spec.spl
DIVERGENT os/compositor/wm_scene_spec.spl
DIVERGENT os/crypto/bip39_kat_spec.spl
DIVERGENT os/crypto/chacha20_simd_parity_spec.spl
DIVERGENT os/crypto/sm3_kat_spec.spl
DIVERGENT os/desktop/desktop_e2e_shortcut_flow_spec.spl
DIVERGENT os/desktop/dock_spec.spl
DIVERGENT os/desktop/shell_baremetal_backend_spec.spl
DIVERGENT os/drivers/framebuffer/fb_driver_spec.spl
DIVERGENT os/drivers/input/ps2_keyboard_spec.spl
DIVERGENT os/drivers/input/ps2_mouse_spec.spl
DIVERGENT os/drivers/nvme/nvme_driver_probe_contract_spec.spl
DIVERGENT os/drivers/nvme/nvme_physical_preflight_script_spec.spl
DIVERGENT os/drivers/nvme/nvme_storage_model_spec.spl
DIVERGENT os/drivers/real_device_readiness_spec.spl
DIVERGENT os/installer/image_builder_artifact_spec.spl
DIVERGENT os/kernel/arch/gdt_layout_spec.spl
DIVERGENT os/kernel/arch/riscv64_interrupt_spec.spl
DIVERGENT os/kernel/arch/riscv64_trap_model_spec.spl
DIVERGENT os/kernel/arch/syscall_dispatch_spec.spl
DIVERGENT os/kernel/arch/syscall_entry_spec.spl
DIVERGENT os/kernel/ipc/execve_spec.spl
DIVERGENT os/kernel/ipc/ipc_error_codes_spec.spl
DIVERGENT os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl
DIVERGENT os/kernel/ipc/ipc_port_create_hosted_spec.spl
DIVERGENT os/kernel/ipc/ipc_spec.spl
DIVERGENT os/kernel/ipc/ipc_syscall_handoff_spec.spl
DIVERGENT os/kernel/ipc/syscall_spec.spl
DIVERGENT os/kernel/loader/app_registry_spec.spl
DIVERGENT os/kernel/loader/dylib_registry_spec.spl
DIVERGENT os/kernel/loader/loader_api_spec.spl
DIVERGENT os/kernel/loader/process_image_spec.spl
DIVERGENT os/kernel/loader/smf_spec.spl
DIVERGENT os/kernel/loader/spawn_pipeline_spec.spl
DIVERGENT os/kernel/loader/x86_64_fs_exec_spawn_spec.spl
DIVERGENT os/kernel/loader/zstd_decompress_spec.spl
DIVERGENT os/kernel/memory/pmm_spec.spl
DIVERGENT os/kernel/memory/vmm_vma_spec.spl
DIVERGENT os/kernel/scheduler/scheduler_spec.spl
DIVERGENT os/kernel/smp/smp_spec.spl
DIVERGENT os/kernel/types/device_mem_types_spec.spl
DIVERGENT os/memory/mold_linker_spec.spl
DIVERGENT os/multiarch/hardening_gates_spec.spl
DIVERGENT os/port/simpleos_multiplatform_build_spec.spl
DIVERGENT os/posix/dylib_async_spec.spl
DIVERGENT os/posix/dynlib_spec.spl
DIVERGENT os/posix/socket_compat_spec.spl
DIVERGENT os/process_isolation_as_spec.spl
DIVERGENT os/proxy/socks5_spec.spl
DIVERGENT os/proxy/stun_spec.spl
DIVERGENT os/qemu_runner_desktop_extended_spec.spl
DIVERGENT os/qemu_runner_desktop_spec.spl
DIVERGENT os/qemu_runner_extended_spec.spl
DIVERGENT os/qemu_runner_raw_image_validator_spec.spl
DIVERGENT os/qemu_runner_spec.spl
DIVERGENT os/services/clock_service_spec.spl
DIVERGENT os/services/devfs_service_spec.spl
DIVERGENT os/services/ds_service_spec.spl
DIVERGENT os/services/llm/ui_access_dispatch_spec.spl
DIVERGENT os/services/llm/widget_eval_spec.spl
DIVERGENT os/services/pipefs_service_spec.spl
DIVERGENT os/services/pm_service/pm_service_spec.spl
DIVERGENT os/services/procfs_service_spec.spl
DIVERGENT os/services/rs_service_spec.spl
DIVERGENT os/services/vfs/nvme_filesystem_mounts_spec.spl
DIVERGENT os/services/vfs/vfs_boot_nvme_lease_spec.spl
DIVERGENT os/services/vfs/vfs_pure_fat_production_guard_spec.spl
DIVERGENT os/services/vfs/vfs_spec.spl
DIVERGENT os/services/wm/wm_service_metadata_spec.spl
DIVERGENT os/simpleos_board_hardening_spec.spl
DIVERGENT os/tls12/tls12_record_handshake_round_trip_spec.spl
DIVERGENT os/tls13/aes256_gcm_sha384_cipher_suite_spec.spl
DIVERGENT os/tls13/cert_verify_ecdsa_spec.spl
DIVERGENT os/tls13/cert_verify_ed25519_spec.spl
DIVERGENT os/tls13/chacha20_poly1305_cipher_suite_spec.spl
DIVERGENT os/tls13/encrypted_extensions_spec.spl
DIVERGENT os/tls13/hello_retry_request_spec.spl
DIVERGENT os/tls13/key_update_spec.spl
DIVERGENT os/tls13/server_accept_spec.spl
DIVERGENT os/userlib/process_spawn_path_spec.spl
DIVERGENT rtl/encode_riscv_spec.spl
DIVERGENT runtime/module_init_spec.spl
DIVERGENT runtime/process_is_running_spec.spl
DIVERGENT sffi/sffi_public_api_spec.spl
DIVERGENT spec/expect_spec.spl
DIVERGENT std/auto_comprehensive_13_spec.spl
DIVERGENT std/auto_comprehensive_17_spec.spl
DIVERGENT std/auto_comprehensive_24_spec.spl
DIVERGENT std/condition_spec.spl
DIVERGENT std/constructor_spec.spl
DIVERGENT std/context_spec.spl
DIVERGENT std/desktop/clipboard_spec.spl
DIVERGENT std/desktop/notification_spec.spl
DIVERGENT std/desktop/shell_open_spec.spl
DIVERGENT std/exp/artifact_spec.spl
DIVERGENT std/exp/config_spec.spl
DIVERGENT std/exp/run_spec.spl
DIVERGENT std/exp/sweep_spec.spl
DIVERGENT std/feature_validation/testing_framework_spec.spl
DIVERGENT std/hooks/hook_registry_spec.spl
DIVERGENT std/mock_direct_spec.spl
DIVERGENT std/mock_phase4_spec.spl
DIVERGENT std/mock_phase5_spec.spl
DIVERGENT std/mock_phase7_spec.spl
DIVERGENT std/mock_recorder_spec.spl
DIVERGENT std/mock_simple_spec.spl
DIVERGENT std/module_import_spec.spl
DIVERGENT std/parser_spec.spl
DIVERGENT std/pending_on_spec.spl
DIVERGENT std/perf_optimization_spec.spl
DIVERGENT std/runtime_parser_bugs_spec.spl
DIVERGENT std/spec_framework_spec.spl
DIVERGENT std/test_meta_spec.spl
DIVERGENT t32_mcp/lifecycle_tools_spec.spl
DIVERGENT test_runner/mode_filter_spec.spl
DIVERGENT tools/cat_spec.spl
DIVERGENT tools/simple_os_primary_spec.spl
--- div_test_02_integration (89 pairs) ---
DIVERGENT app/app_mcp_intensive_spec.spl
DIVERGENT app/check_log_modes_spec.spl
DIVERGENT app/cli_log_modes_spec.spl
DIVERGENT app/feature_gen_log_modes_spec.spl
DIVERGENT app/io_runtime_import_spec.spl
DIVERGENT app/itf_log_modes_spec.spl
DIVERGENT app/linkers_log_modes_spec.spl
DIVERGENT app/llm_dashboard_log_modes_spec.spl
DIVERGENT app/loader_exec_memory_spec.spl
DIVERGENT app/mcp_stdio_integration_spec.spl
DIVERGENT app/optimize/optimize_cli_spec.spl
DIVERGENT app/os_log_modes_spec.spl
DIVERGENT app/primitive_api_lint_spec.spl
DIVERGENT app/simple_lsp_mcp_stdio_spec.spl
DIVERGENT app/simple_portal/simple_portal_content_db_spec.spl
DIVERGENT app/simple_portal/simple_portal_server_spec.spl
DIVERGENT app/spec_coverage_log_modes_spec.spl
DIVERGENT app/spipe_quality_lint_spec.spl
DIVERGENT app/startup_argparse_mmap_perf_spec.spl
DIVERGENT app/todo_parser_cli_test.spl
DIVERGENT app/ui_browser_log_modes_spec.spl
DIVERGENT app/ui/main_render_spec.spl
DIVERGENT app/ui.web/capability_gating_spec.spl
DIVERGENT app/ui.web/reconnect_test.spl
DIVERGENT app/ui.web/wm_bridge_test.spl
DIVERGENT app/ui.web/ws_e2e_spec.spl
DIVERGENT app/verify_log_modes_spec.spl
DIVERGENT app/verify_test_quality_gate_spec.spl
DIVERGENT app/web_stack_sample_browser_spec.spl
DIVERGENT app/web_stack_sample_persistence_runner.spl
DIVERGENT app/web_stack_sample_persistence_spec.spl
DIVERGENT app/web_stack_sample_spec.spl
DIVERGENT baremetal/remote_riscv32_spec.spl
DIVERGENT compiler/advanced_types_spec.spl
DIVERGENT compiler/import_syntax_spec.spl
DIVERGENT compiler/llvm_compiled_proof_spec.spl
DIVERGENT compiler/llvm_native_link_spec.spl
DIVERGENT compiler/llvm_parity_spec.spl
DIVERGENT compiler/native_backend_e2e_spec.spl
DIVERGENT compiler/static_method_desugar_spec.spl
DIVERGENT compiler/vhdl_backend_e2e_spec.spl
DIVERGENT examples/platform_library_example_spec.spl
DIVERGENT ffi_gen/math_migration_test.spl
DIVERGENT fs_driver/capability_dispatch_test.spl
DIVERGENT fs_driver/multi_mount_test.spl
DIVERGENT hardware/rv32imac/rv32_core_smoke_spec.spl
DIVERGENT http_baremetal_spec.spl
DIVERGENT io/native_ops_dir_create_all_spec.spl
DIVERGENT io/native_ops_dir_create_spec.spl
DIVERGENT io/native_ops_dir_recursive_spec.spl
DIVERGENT io/native_ops_file_copy_spec.spl
DIVERGENT io/native_ops_file_read_write_spec.spl
DIVERGENT io/native_ops_file_size_spec.spl
DIVERGENT lib/std/doctest/discovery_spec.spl
DIVERGENT lib/std/improvements/stdlib_improvements_spec.spl
DIVERGENT lib/thread_pool_async_spec.spl
DIVERGENT log_facade_back_compat_spec.spl
DIVERGENT net/http_content_encoding_spec.spl
DIVERGENT os/port/bootstrap_cross_status_spec.spl
DIVERGENT os/port/disk_image_bake_spec.spl
DIVERGENT os/port/llvm/cross_build_plan_spec.spl
DIVERGENT os/port/llvm/per_target_build_spec.spl
DIVERGENT os/port/llvm/smoke_clang_spec.spl
DIVERGENT os/port/native_convergence_spec.spl
DIVERGENT os/port/rust/smoke_rustc_spec.spl
DIVERGENT remote_jit/arduino_r4_composite_runner_spec.spl
DIVERGENT remote_jit/esp32_composite_runner_spec.spl
DIVERGENT rendering/backend_screenshot_compare_spec.spl
DIVERGENT rendering/engine2d_backend_spec.spl
DIVERGENT rendering/helpers_parity_spec.spl
DIVERGENT rendering/metal_msl_pipeline_spec.spl
DIVERGENT rendering/pixel_verify_browser_glass.spl
DIVERGENT rendering/pixel_verify_debug.spl
DIVERGENT rendering/pixel_verify_full.spl
DIVERGENT rendering/pixel_verify_main.spl
DIVERGENT rendering/pixel_verify_scene.spl
DIVERGENT rendering/pixel_verify_simple.spl
DIVERGENT rendering/pixel_verify_style.spl
DIVERGENT simpleos_driver_log_smoke_spec.spl
DIVERGENT spec/runner_spec.spl
DIVERGENT stats_command_spec.spl
DIVERGENT storage/dbfs/dbfs_engine_checkpoint_ring_spec.spl
DIVERGENT storage/dbfs/dbfs_engine_checkpoint_spec.spl
DIVERGENT storage/dbfs/dbfs_engine_pager_spec.spl
DIVERGENT storage/dbfs/dbfs_nvme_callback_spec.spl
DIVERGENT storage/dbfs/dbfs_posix_shim_spec.spl
DIVERGENT storage/dbfs/dbfs_ring_diag_spec.spl
DIVERGENT storage/dbfs/mount_table_dbfs_dispatch_spec.spl
DIVERGENT t32_hw/50_session_close_spec.spl
--- div_test_03_system_feature (81 pairs) ---
DIVERGENT lib/mcp/bootstrap_e2e_test.spl
DIVERGENT lib/mcp/bootstrap_import_test.spl
DIVERGENT lib/mcp/bootstrap_protocol_test.spl
DIVERGENT lib/mcp/handler_function_test.spl
DIVERGENT lib/mcp/handler_import_test.spl
DIVERGENT lib/mcp/simple_import_test.spl
DIVERGENT lib/minimal_spec.spl
DIVERGENT lib/std/compiler/lexer_ffi_test.spl
DIVERGENT ml/tensor_dimensions_spec.spl
DIVERGENT mode_filter/skip_native_spec.spl
DIVERGENT plugin/sugar_plugin_spec.spl
DIVERGENT scilib/cuda_device_buffer_spec.spl
DIVERGENT scilib/df_construction_spec.spl
DIVERGENT scilib/linalg_backend_diagnostics_spec.spl
DIVERGENT scilib/linalg_cuda_backend_spec.spl
DIVERGENT scilib/linalg_openblas_backend_spec.spl
DIVERGENT scilib/linalg_simd_spec.spl
DIVERGENT scilib/linalg_torch_backend_spec.spl
DIVERGENT scilib/ndarray_broadcast_spec.spl
DIVERGENT scilib/ndarray_dtype_spec.spl
DIVERGENT scilib/ndarray_reduction_spec.spl
DIVERGENT scilib/ndarray_simd_spec.spl
DIVERGENT scilib/ndarray_ufunc_spec.spl
DIVERGENT scilib/simd_f32_spec.spl
DIVERGENT usage/alias_deprecated_spec.spl
DIVERGENT usage/aop_architecture_rules_spec.spl
DIVERGENT usage/aop_spec.spl
DIVERGENT usage/btree_basic_spec.spl
DIVERGENT usage/capability_system_spec.spl
DIVERGENT usage/class_invariant_spec.spl
DIVERGENT usage/cmm_lsp/bulk_validate_spec.spl
DIVERGENT usage/cmm_lsp/cmm_lexer_spec.spl
DIVERGENT usage/cmm_lsp/cmm_parser_expr_spec.spl
DIVERGENT usage/cmm_lsp/cmm_parser_spec.spl
DIVERGENT usage/cmm_lsp/cmm_parse_v4_fixes_spec.spl
DIVERGENT usage/cmm_lsp/string_efficiency_spec.spl
DIVERGENT usage/contract_persistence_feature_spec.spl
DIVERGENT usage/effect_system_spec.spl
DIVERGENT usage/enums_spec.spl
DIVERGENT usage/exists_check_spec.spl
DIVERGENT usage/exists_check_value_return_spec.spl
DIVERGENT usage/extern_functions_spec.spl
DIVERGENT usage/function_alias_spec.spl
DIVERGENT usage/generic_bytecode_spec.spl
DIVERGENT usage/gpu_kernel_launch_spec.spl
DIVERGENT usage/gpu_ptx_gen_spec.spl
DIVERGENT usage/hashmap_basic_spec.spl
DIVERGENT usage/hm_type_inference_spec.spl
DIVERGENT usage/line_continuation_spec.spl
DIVERGENT usage/llvm_backend_aarch64_spec.spl
DIVERGENT usage/llvm_backend_arm32_spec.spl
DIVERGENT usage/llvm_backend_i686_spec.spl
DIVERGENT usage/llvm_backend_riscv32_spec.spl
DIVERGENT usage/llvm_backend_riscv64_spec.spl
DIVERGENT usage/llvm_backend_spec.spl
DIVERGENT usage/math_autograd_runtime_spec.spl
DIVERGENT usage/math_dl_equations_spec.spl
DIVERGENT usage/no_paren_calls_spec.spl
DIVERGENT usage/note_sdn_feature_spec.spl
DIVERGENT usage/null_coalescing_try_operator_spec.spl
DIVERGENT usage/pass_variants_spec.spl
DIVERGENT usage/pattern_matching_advanced_spec.spl
DIVERGENT usage/static_const_declarations_spec.spl
DIVERGENT usage/string_interpolation_spec.spl
DIVERGENT usage/table_spec.spl
DIVERGENT usage/trait_forwarding_spec.spl
DIVERGENT usage/trait_keyword_all_phases_spec.spl
DIVERGENT usage/wasm_compile_spec.spl
DIVERGENT usage/x86_boot_spec.spl
DIVERGENT web_platform/css/animations_wpt_spec.spl
DIVERGENT web_platform/css/at_supports_wpt_spec.spl
DIVERGENT web_platform/css/background_gradient_wpt_spec.spl
DIVERGENT web_platform/css/box_shadow_wpt_spec.spl
DIVERGENT web_platform/css/custom_properties_wpt_spec.spl
DIVERGENT web_platform/css/glass_feature_gap_spec.spl
DIVERGENT web_platform/css/object_fit_wpt_spec.spl
DIVERGENT web_platform/css/pseudo_text_wpt_spec.spl
DIVERGENT web_platform/css/scrollbar_wpt_spec.spl
DIVERGENT web_platform/css/selector_color_subset_spec.spl
DIVERGENT web_platform/css/sticky_wpt_spec.spl
DIVERGENT web_platform/css/transforms_wpt_spec.spl
--- div_test_03_system (62 pairs) ---
DIVERGENT app/browser/feature/webgpu_js_wasm_simple_spec.spl
DIVERGENT app/compiler/feature/all_regions_spec.spl
DIVERGENT app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl
DIVERGENT app/compiler/feature/target_instruction_optimization_32bit_spec.spl
DIVERGENT app/compiler/feature/world_units_newunit_spec.spl
DIVERGENT app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl
DIVERGENT app/hardware/feature/riscv_fpga_linux_spec.spl
DIVERGENT app/hardware/feature/riscv_linux_rtl_dual_arch_completion_spec.spl
DIVERGENT app/native_build/feature/executable_size_reduction_spec.spl
DIVERGENT app/os/feature/rv64_user_mode_exec_spec.spl
DIVERGENT app/os/feature/simpleos_desktop_core_formal_verification_spec.spl
DIVERGENT app/os/feature/ui_access_protocol_spec.spl
DIVERGENT app/os/feature/vfs_exec_bytes_spec.spl
DIVERGENT app/simpleos/feature/simpleos_riscv_smf_fs_launch_spec.spl
DIVERGENT app/simpleos/feature/simpleos_rv64_hosted_qemu_spec.spl
DIVERGENT app/simpleos/feature/simpleos_wine_proton_steam_impl_spec.spl
DIVERGENT app/ui/feature/shared_wm_renderer_unification_spec.spl
DIVERGENT app/vscode_extension/feature/vscode_math_editor_panel_spec.spl
DIVERGENT app/vscode_rich_editor/feature/vscode_rich_editor_spec.spl
DIVERGENT compiler/backend_port_system_spec.spl
DIVERGENT compiler/compiler_interpret_pipeline_spec.spl
DIVERGENT compiler/driver_api_external_facade_spec.spl
DIVERGENT compiler/driver_api_heavy_path_spec.spl
DIVERGENT compiler/driver_api_tier_policy_spec.spl
DIVERGENT compiler/effects_core_spec.spl
DIVERGENT compiler/parser_improvements_spec.spl
DIVERGENT compiler/string_escape_spec.spl
DIVERGENT compiler/vhdl_source_facade_spec.spl
DIVERGENT coverage/coverage_runtime_ffi_spec.spl
DIVERGENT coverage/coverage_test_runner_spec.spl
DIVERGENT database/server/db_durability_spec.spl
DIVERGENT database/server/db_server_tier_spec.spl
DIVERGENT gui/arm64_wm_qemu_contract_spec.spl
DIVERGENT gui/arm64_wm_ramfb_screendump_spec.spl
DIVERGENT gui/event_processing_spec.spl
DIVERGENT gui/glass_pixel_compare_spec.spl
DIVERGENT gui/headless_rendering_spec.spl
DIVERGENT gui/native_gui_build_spec.spl
DIVERGENT gui/sdn_parsing_spec.spl
DIVERGENT gui/tui_screen_spec.spl
DIVERGENT gui/web_api_json_spec.spl
DIVERGENT gui/web_api_spec.spl
DIVERGENT gui/widget_rendering_spec.spl
DIVERGENT gui/wm_input_qemu_smoke_spec.spl
DIVERGENT hardware/riscv64_fpga/hardware_inventory_spec.spl
DIVERGENT hardware/riscv64_fpga/hello_payload_spec.spl
DIVERGENT hardware/riscv64_fpga/jtag_unbind_spec.spl
DIVERGENT hardware/riscv64_fpga/preflight_spec.spl
DIVERGENT hardware/rv32_external_formal_harness_spec.spl
DIVERGENT infrastructure/coverage_system_spec.spl
DIVERGENT interpreter/interpreter_bugs_spec.spl
DIVERGENT interpreter/lazy_shb_probe.spl
DIVERGENT interpreter/lazy_shb_system_spec.spl
DIVERGENT net_connect_completion_spec.spl
DIVERGENT os/boot_smoke_spec.spl
DIVERGENT os_crypto_ref_helpers.spl
DIVERGENT os/e2e/simple_from_fs_spec.spl
DIVERGENT os/port/alt_rootfs_disk_boot_spec.spl
DIVERGENT os/port/clang_static_e2e_spec.spl
DIVERGENT os/port/dbfs_disk_boot_spec.spl
DIVERGENT os/simpleos_ai_cli_js_node_port_spec.spl
DIVERGENT tools/deploy/smoke_spec.spl
--- div_test_05_perf (18 pairs) ---
DIVERGENT bench/db_accel_index/db_accel_index_spec.spl
DIVERGENT bench/jit_minimal_test.spl
DIVERGENT cli_dispatch_perf_spec.spl
DIVERGENT ctype/bench_ctype_static_lut.spl
DIVERGENT ctype/ctype_lut_tables.spl
DIVERGENT ctype/global_static_array_smoke.spl
DIVERGENT graphics_2d/bench_2d_metal_simple_jit.spl
DIVERGENT graphics_2d/bench_2d_metal_simple.spl
DIVERGENT graphics_2d/bench_2d_vulkan.spl
DIVERGENT graphics_2d/perf_2d_runner.spl
DIVERGENT graphics_2d/simple_runner.spl
DIVERGENT graphics_2d/vulkan_spirv_spec.spl
DIVERGENT llvm_lib_ffi_perf_spec.spl
DIVERGENT local_gpu_check/run_gpu_check.spl
DIVERGENT tauri_equiv/gui_vs_tauri_spec.spl
DIVERGENT tauri_equiv/report_spec.spl
DIVERGENT ui_access/ui_access_hot_paths_spec.spl
DIVERGENT web_render_chrome/web_paint_cache_spec.spl
```
