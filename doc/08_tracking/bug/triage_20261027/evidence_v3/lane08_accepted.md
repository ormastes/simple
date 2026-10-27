# V3 lane 08 accepted evidence

Accepted classifications in this lane: 43. Frozen assessment source: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

## stage2_cross_module_codec_result_field_inference_2026-08-14 — Stage 2 cannot infer field type of a cross-module codec result struct field

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_cross_module_codec_result_field_inference_2026-08-14.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_cross_module_codec_result_field_inference_2026-08-14.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/provider_cli/native_provider_v1.spl:40](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/provider_cli/native_provider_v1.spl#L40); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:312](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl#L312)
- Review rationale: Report documents lost .ok field type across encode_provider_query_result_v1. Current provider explicitly annotates both codec results; module surface conversion retains declared return_type, so the loss site is not established. Annotation is a workaround, not a diagnosed compiler remedy.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## stage2_link_undefined_module_surfaces_promote_reason_sffi_enum_discriminant_2026-09-13 — Site 17: Stage 2 does not LINK on `origin/main` — `module_surfaces_promote_reason` and `_sffi_enum_discriminant` undefined

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_link_undefined_module_surfaces_promote_reason_sffi_enum_discriminant_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_link_undefined_module_surfaces_promote_reason_sffi_enum_discriminant_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/module_surface_registry.spl:608](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/module_surface_registry.spl#L608); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:51](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl#L51)
- Review rationale: Report's two missing names are historical: current promotion helper exists and method_calls_literals uses its own rt_enum_discriminant wrapper rather than importing private helper calls. This reduces the specific source holes but does not establish the seed private-name-resolution root remedy or current link qualification.
- Review corrections: solution: known -> unknown; structural_change: no -> unknown; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## stage2_matrix_cg_modules_managed_tool_projection_invalid_2026_10_20 — Stage 2 matrix src/app/_cg modules: managed tool projection role/path/digest invalid

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_matrix_cg_modules_managed_tool_projection_invalid_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_matrix_cg_modules_managed_tool_projection_invalid_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/native_tool_authority_v1.spl:91](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io/native_tool_authority_v1.spl#L91)
- Review rationale: Seven module compilations historically failed projection validation. Decoder checks role, canonical path and digest together at lines91-94; current linker role accepts mold. The failure string does not identify which supplied pin failed, so neither faulty producer versus validator nor local structural scope is diagnosed. Retain guards.
- Review corrections: structural_change: no -> unknown; independent target review; historical execution is not a current receipt.

## stage2_matrix_test_runner_build_no_c_compiler_for_empty_module_object_2026_10_20 — Stage 2 matrix test_runner_build: no C compiler available for empty module object

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_matrix_test_runner_build_no_c_compiler_for_empty_module_object_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_matrix_test_runner_build_no_c_compiler_for_empty_module_object_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:4306](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_aot_native_output.spl#L4306)
- Review rationale: Current empty-MIR branch writes a C unit and calls find_c_compiler, returning the reported error when it is empty. Historical source line4245 moved to4326. Host C availability does not prove task projection carries that compiler; inspect matrix environment and compiler-discovery owner next. No root fix or structural scope established.
- Review corrections: structural_change: no -> unknown; independent target review; historical execution is not a current receipt.

## stage2_msvc_link_error_payload_invalid_heap_2026-09-03 — Stage 2 MSVC link failure is UNDIAGNOSABLE: the Err payload interpolates to `<invalid-heap:0x...>`

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_msvc_link_error_payload_invalid_heap_2026-09-03.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_msvc_link_error_payload_invalid_heap_2026-09-03.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl:2728](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl#L2728)
- Review rationale: Report separates damaged Err payload from unknown MSVC linker failure. Current wrapper uses typed e.message rather than the old e interpolation at2734, but still crosses linker.link Result boundary. No ABI/payload lifetime remedy was demonstrated; copying stderr would diagnose or bypass, not establish root fix.
- Review corrections: solution: known -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## stage2_msvc_link_uses_gnu_driver_flags_2026-09-12 — Stage 2 link passes GNU driver flags to cl.exe (Windows/MSVC)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_msvc_link_uses_gnu_driver_flags_2026-09-12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_msvc_link_uses_gnu_driver_flags_2026-09-12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:1890](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/pipeline/native_project/linker.rs#L1890); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:2635](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/pipeline/native_project/linker.rs#L2635)
- Review rationale: Full report's concrete MSVC driver correction is present: /Fe output, /INCLUDE accumulation and single trailing /link group; GNU branch retains -o. Existing flavor test is narrow and clang-cl run is historical. Root correction fits existing linker contract; real cl.exe Stage2 qualification remains outstanding.

## stage2_parent_receipt_publish_passes_wrong_candidate_path_2026-09-13 — Site 14: Stage 2 is ADMITTED, then the parent-receipt publisher is handed the wrong candidate path, and Stage 3 cannot be admitted

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_parent_receipt_publish_passes_wrong_candidate_path_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_parent_receipt_publish_passes_wrong_candidate_path_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:4820](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-from-scratch.sh#L4820); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/publish-stage2-parent-receipts.shs:44](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/publish-stage2-parent-receipts.shs#L44)
- Review rationale: Full report pins publisher mismatch between mutable stage2_bin and immutable receipt candidate. Current bootstrap passes stage2_admitted_absolute, while publisher retains exact candidate_path equality guard. Concrete local call-argument remedy already exists, unchanged from inventory; source-matched receipt test still needed.
- Review corrections: inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> fixed_pending_verification; independent target review; historical execution is not a current receipt.

## stage2_receiver_probe_module_path_naming_not_run_2026-09-14 — Stage 2 receiver probe intermittently reports `compiler.common.module_path_naming` as NOT_RUN

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_receiver_probe_module_path_naming_not_run_2026-09-14.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_receiver_probe_module_path_naming_not_run_2026-09-14.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:821](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_aot_native_output.spl#L821); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:2853](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_aot_native_output.spl#L2853)
- Review rationale: Full report explicitly leaves underlying transient open after attribution fix. Current postprocess consults dispatch count and names capsule failure when attempted>=scheduled, preserving NOT_RUN only for undispatched work. That repairs misleading label, not the unstable capsule invariant; do not classify symptom bookkeeping as root fix.
- Review corrections: solution: known -> unknown; structural_change: no -> unknown; recommended_action: fixed_pending_verification -> keep_open; independent target review; historical execution is not a current receipt.

## stage2_receiver_probe_module_path_naming_not_run_flake_2026-09-14 — Stage 2 receiver probe intermittently loses `compiler.common.module_path_naming` (NOT_RUN)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_receiver_probe_module_path_naming_not_run_flake_2026-09-14.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_receiver_probe_module_path_naming_not_run_flake_2026-09-14.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:821](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_aot_native_output.spl#L821); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_receiver_probe_module_path_naming_not_run_2026-09-14.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage2_receiver_probe_module_path_naming_not_run_2026-09-14.md)
- Review rationale: Original flake report infers scheduling race from NOT_RUN, but companion full report and current attempted-count helper show an already-run capsule can fail later validation. Flake remains historically evidenced; root race claim is unproven and duplication is not invalidity.
- Review corrections: inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## stage3_bootstrap_closure_lowered_without_providers_2026_10_20 — Stage 3 bootstrap-fixed closure and entry modules lowered with no providers (47,497 MIR errors)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_bootstrap_closure_lowered_without_providers_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_bootstrap_closure_lowered_without_providers_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_pipeline_lowering.spl:1182](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_pipeline_lowering.spl#L1182); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2244](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLowering/module_lowering.spl#L2244)
- Review rationale: Full report pins empty provider lists. Current driver passes ctx.mir_feed_modules to both closure and entry lowering; entry helper forwards providers explicitly to lower_module. This corrects existing data-feed omission locally. Historical probe passed; full-closure qualification remains missing.

## stage3_bootstrap_closure_provider_registration_cost_2026_10_20 — Stage 3 bootstrap-fixed closure provider registration costs 12.8 s and RSS +28 MB per module (r8 base)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_bootstrap_closure_provider_registration_cost_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_bootstrap_closure_provider_registration_cost_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2808](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLowering/module_lowering.spl#L2808); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2922](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLowering/module_lowering.spl#L2922)
- Review rationale: Full report explicitly measures old r8 base lacking demand/provider-session optimizations. Current module_lowering branches on declaration_repository, lazy provider methods and session enum rows, so old12.8s/provider costs cannot be applied unchanged. Need fresh per-section profile; neither current fix nor remaining allocation cause is established.
- Review corrections: inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## stage3_bootstrap_real_llvm_imported_global_undeclared_2026_10_20 — Stage 3 bootstrap real-LLVM entry IR loads imported pub val globals without declaring them

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_bootstrap_real_llvm_imported_global_undeclared_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_bootstrap_real_llvm_imported_global_undeclared_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:664](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl#L664); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:3167](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl#L3167)
- Review rationale: Full report's imported-global omission remains in emit_bootstrap_statics: external rows immediately continue at672-674, while scalar load-global code references those symbols and ordinary emitter declares externals at494-498. Concrete local remedy: emit deduplicated typed external global declarations for external rows, retaining provider definitions and avoiding duplicate declarations. Current execution untested.

## stage3_closure_loop_rss_growth_after_provider_feed_2026_10_20 — Stage 3 closure loop RSS grows 20-36 MB per module with the provider feed (52 GiB cap nearly exhausted)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_closure_loop_rss_growth_after_provider_feed_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_closure_loop_rss_growth_after_provider_feed_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2808](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLowering/module_lowering.spl#L2808)
- Review rationale: Full report records20-36MB/module growth after transient scope and provider feed fixes, with no MIR heap/RSS split. Current provider registration includes repository/demand branches; these do not prove allocator or retained ownership correction. Root cause and structural scope remain unknown pending fixed-tree MIR profile.
- Review corrections: inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## stage3_coordinator_route_cold_init_unreachable_under_env_i_2026-09-14 — Stage 3 coordinator route is unusable on a cold checkout: its own remedy cannot reach the child

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_coordinator_route_cold_init_unreachable_under_env_i_2026-09-14.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_coordinator_route_cold_init_unreachable_under_env_i_2026-09-14.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/resume-stage3-from-admitted.sh:952](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/resume-stage3-from-admitted.sh#L952)
- Review rationale: Full report tracks unreachable cold-init remedy under env-i plus unused fallback. Current resume script validates explicit cold-init opt-in and assembles stage3_cold_init_env at952-956, so forwarding has source support; complete child argv and fallback policy need checking before fixed status. Guard refusal is not invalid.
- Review corrections: solution: known -> unknown; structural_change: no -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## stage3_hard_blocked_on_stage2_admission_2026-08-31 — Stage 3 is hard-blocked on Stage-2 admission (2026-08-31, aarch64-apple-darwin)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_hard_blocked_on_stage2_admission_2026-08-31.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_hard_blocked_on_stage2_admission_2026-08-31.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:150](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs#L150)
- Review rationale: Full report records real missing admitted parent and E-MIR-TYPE-Unknown prerequisite failure, then later historical Stage2 admission. Current producer still correctly demands canonical parent, sanity/provenance receipts and matching admission digest. Correct guard does not make original blocker false. Current platform-qualified admission evidence absent; no invalid closure.
- Review corrections: validity: uncertain -> valid; inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## stage3_hir_cache_direct_route_misses_sharded_entries_2026_10_20 — Stage 3 HIR cache: direct route misses every entry the sharded route stored

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_hir_cache_direct_route_misses_sharded_entries_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_hir_cache_direct_route_misses_sharded_entries_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_cache.spl:250](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_hir_cache.spl#L250)
- Review rationale: Full report compares2280-module sharded and1352-module direct routes. Current key normalizes relative path but also hashes closure digest, entry mode, environment/target and codec; load supports root rebasing. Same file alone therefore does not prove identical cache identity. Need compare retained key components before narrowing remedy; missing reuse is a valid historical issue.
- Review corrections: structural_change: no -> unknown; inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## stage3_hir_cache_reencode_selfcheck_and_low_store_rate_2026_10_19 — Stage 3 HIR cache logs reencode SELFCHECK failures and stores only 25 of 771 lowered modules

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_hir_cache_reencode_selfcheck_and_low_store_rate_2026_10_19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_hir_cache_reencode_selfcheck_and_low_store_rate_2026_10_19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_cache.spl:619](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_hir_cache.spl#L619); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_cache.spl:989](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_hir_cache.spl#L989)
- Review rationale: Full report's expected10/got0 selfcheck is an actual codec disagreement, not a wrong cache guard. Current selfcheck decodes, reencodes and refuses differences with field diagnostics; optional reencode admission is separate. Need failing blob to locate field loss and silent store eligibility; unknown root and scope retained.
- Review corrections: inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22 — Stage 3 streaming HIR owner crashes after export-origin convergence

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage3_streaming_hir_owner_crash_after_origin_fix_2026-08-22.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1029](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_hir_pipeline_lowering.spl#L1029)
- Review rationale: Full report identifies streaming owner handoff before first HIR progress and says zero ctx.modules is intentional. Current streaming path reads retained owner directly and rejects malformed payload via rt_heap_ref_wellformed before fields; readiness and empty-surface guards remain. This prevents unsafe use but does not prove original producer/lifetime repair or Stage3 success.
- Review corrections: structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## stage4_driver_backend_result_sdnvalue_import_2026-08-02 — Stage 4 driver BackendResult payload import gap

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_driver_backend_result_sdnvalue_import_2026-08-02.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stage4_driver_backend_result_sdnvalue_import_2026-08-02.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_types.spl:38](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_types.spl#L38); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend_types.spl:45](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/70.backend/backend_types.spl#L45)
- Review rationale: Full report pins missing backend-local payload identity. Current BackendResult.SdnData uses BackendSdnValue; backend owner exports it and CompiledUnit, and driver_types explicitly imports both alongside BackendResult. Existing-module identity/import repair is present; historical focused HIR evidence is not current Stage4 qualification.

## stale_spec_cluster_premise_false_148_live_specs_2026-08-23 — The "148 stale specs" cluster is NOT stale — the APIs exist, and deleting these specs would have destroyed live coverage

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stale_spec_cluster_premise_false_148_live_specs_2026-08-23.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stale_spec_cluster_premise_false_148_live_specs_2026-08-23.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir.spl:15](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/mir.spl#L15); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_lowering_types.spl:35](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/mir_lowering_types.spl#L35)
- Review rationale: Full report tracks false stale-spec classification risking live coverage deletion; it does not endorse the refuted missing-API premise. Current MirLowering struct exists and mir facade imports rather than explicitly reexports its families, matching the worked surface problem. Exact148-member census not revalidated, so conservative root/scope unknown; no invalid closure or test deletion.
- Review corrections: validity: uncertain -> valid; inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## std_collection_helpers_module_missing_2026-09-01 — `std.collection_helpers` module does not exist — spec covers 33+ unimplemented functions

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/std_collection_helpers_module_missing_2026-09-01.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/std_collection_helpers_module_missing_2026-09-01.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/collection_helpers.spl (absent](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/collection_helpers.spl (absent); `history2cca0bc59c4)`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/std/common/collection_helpers_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/lib/std/common/collection_helpers_spec.spl)
- Review rationale: Full report tracks70+ examples importing missing collection_helpers module. Exact current path absent; bounded target file census finds only spec and summaries, with deletion history rather than implementation. This is intentionally tracked missing functionality; implement-features is not a diagnosed known root remedy or automatically structural change.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## std_crypto_sha1_missing_hex_upper_2026-07-20 — `std.crypto.sha1` (array-based) lacks `sha1_hex_upper` present in the sibling `std.common.crypto.sha1` (text-based) module

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/std_crypto_sha1_missing_hex_upper_2026-07-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/std_crypto_sha1_missing_hex_upper_2026-07-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/crypto/sha1.spl:107](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/crypto/sha1.spl#L107); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/crypto/sha1.spl:267](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/crypto/sha1.spl#L267)
- Review rationale: Full report's missing uppercase wrapper is already repaired: array-based module sha1_hex_upper(text) calls existing text-to-bytes sha1_hex then to_upper at113-114. Text-based sibling has matching API. Local additive wrapper addresses import gap without switching every spec call to other SHA1 owner; runtime/import qualification remains untested.
- Review corrections: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fixed_pending_verification; independent target review; historical execution is not a current receipt.

## std_io_runtime_ranged_read_export_missing_2026_10_10 — Root io_runtime facade omits checked ranged read

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/std_io_runtime_ranged_read_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/lib/std_io_runtime_ranged_read_spec.spl); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/std_io_runtime_ranged_read_export_missing_2026_10_10.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/std_io_runtime_ranged_read_export_missing_2026_10_10.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/io_runtime.spl:20](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/io_runtime.spl#L20); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/sosix/host_facade.spl:65](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_async_mut/sosix/host_facade.spl#L65)
- Review rationale: Canonical report fully read and four fixtures inspected. Root io_runtime facade now exports file_read_text_at_nullable via SoSix host_facade, which reexports the same checked io owner under original and sosix names. This is existing declaration export repair with no new runtime wrapper; authored range/negative/missing/zero-size assertions are unexecuted.

## stray_vgate_probe_tag_2026-09-07 — `vgate-probe-004312` is a stray tag that nobody can delete

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stray_vgate_probe_tag_2026-09-07.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/stray_vgate_probe_tag_2026-09-07.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:.claude/rules/vcs.md:189](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/.claude/rules/vcs.md#L189)
- Review rationale: Full report records actual successful probe tag creation followed by GH013 deletion refusal. Target VCS rule explicitly names same incident and prohibits future v-prefixed probes. Investigator-created does not make cleanup issue false. No protected-control weakening proposed; current remote presence/ruleset and permitted cleanup remain unverified.
- Review corrections: solution: known -> unknown; structural_change: no -> unknown; inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## strict-field-forwarding-opt-in-20261027 — src-compiler-has-undefined-field-reads (strict field forwarding opt-in)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/strict_field_forwarding_opt_in_workaround_2026-10-27.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/strict_field_forwarding_opt_in_workaround_2026-10-27.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/accessor_forwarding.spl:16](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Expressions/accessor_forwarding.spl#L16)
- Review rationale: Full report explicitly calls same-file zero-warning census a lower bound, excluding imported owners. Current code caches strict opt-in and emits deduplicated W-HIR-FIELD-001 by default. Missing hard error is a real workaround debt; complete graph offenders and unconditional-enforcement compatibility remain unproven, so no known root fix.

## string_char_code_at_o_index_fallback_on_non_ascii_text_2026-08-28 — `text.char_code_at(i)` is O(i) on any string containing a non-ASCII byte at or before `i`

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/string_char_code_at_o_index_fallback_on_non_ascii_text_2026-08-28.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/string_char_code_at_o_index_fallback_on_non_ascii_text_2026-08-28.md); `src/runtime/runtime_native.c:4438-4491`
- Review rationale: Full report and complete runtime char_code_at implementation inspected: ASCII fast path exists but multibyte indexing restarts decoding from byte zero. This supports the repeated-index cost mechanism. Cache/iterator remedy and present whole-call performance remain unproved; historical measurements are not current reproduction.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## stringlit_optional_array_owner_2026_10_11 — String interpolation optional array loses traversal type

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/mono/monomorphize/stringlit_type_substitution_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/mono/monomorphize/stringlit_type_substitution_spec.spl); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize/type_subst.spl:745](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/40.mono/monomorphize/type_subst.spl#L745)
- Review rationale: Frozen description pins optional interpolation array becoming MIR Tuple; current substitution explicitly binds [HirInterpolation] after optional binding, charges work then recursively substitutes each expression. Focused spec tests wrapped/unwrapped/cache paths and absent/present-empty. Annotation is marked workaround; underlying optional-owner lowering loss not diagnosed, current execution untested.

## svmg_d4_lowering_deferred_subset_2026-08-07 — SVM-G D4 lowering leaves 2 in-subset constructs unimplemented

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/backend/svmg_lowering_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/backend/svmg_lowering_spec.spl); `doc/08_tracking/bug/svmg_d4_lowering_deferred_subset_2026-08-07.md`; `src/compiler/70.backend/svmg_lowering.spl:415-432,543-555`
- Review rationale: Full canonical report plus current lower_print and Assign branches confirm two explicit in-subset rejections: integer print and float compound assignment. Existing integer print/float conversion contracts need implementation review before a complete remedy is known. The sibling f-string parse failure prevents historical spec results from proving current behavior.
- Review corrections: validity: uncertain -> valid; independent target review; historical execution is not a current receipt.

## svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07 — Device single-buffer code/data co-residency diverges from ref_vm's separate code array

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl); `doc/08_tracking/bug/svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07.md`; `src/lib/common/svmg/ref_vm.spl:456-473`
- Review rationale: Full canonical report explains byte50 overlapping PUSHI immediate and reports live-device mismatch; current reference VM still fetches self.code at step458. Device kernel and intended write-to-code contract were not fully audited, so selecting snapshot semantics, moving vector or accepting divergence is not a known fix. Keep semantic gap open, untested.

## t15_hir_forward_decl_target_pass_does_not_exist_2026-08-07 — HirForwardDecl lowering pass has zero production callers; src/app/desugar unreachable from

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:NONE](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/NONE); `doc/08_tracking/bug/t15_hir_forward_decl_target_pass_does_not_exist_2026-08-07.md`; `src/compiler/20.hir/hir_forward_decl.spl:59-76`
- Review rationale: Recovered full planning-defect report; current complete HirForwardDecl module explicitly remains outside HIR union/pipeline and populated metadata does not replace offline text generator. Missing planned integration is a valid issue even without a code regression. Full native grammar/caller census and selected replacement design are absent, so no known root remedy.
- Review corrections: validity: uncertain -> valid; independent target review; historical execution is not a current receipt.

## tail_if_mixed_int_float_arms_lose_the_float_2026-09-06 — Tail `if` with one float arm and one integer arm loses the value (JIT)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tail_if_mixed_int_float_arms_lose_the_float_2026-09-06.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/tail_if_mixed_int_float_arms_lose_the_float_2026-09-06.md); `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs:65-78,1395-1404`
- Review rationale: Full report plus current if_merge_local_ty confirm mixed typed arms fall back to I64; caller allocates that merge slot. Report shows F64-only substitution is insufficient because store conversion is missing. Proper contextual HIR coercion versus arm conversion has not been resolved; retain valid untested unknown solution rather than claim a one-line remedy.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## test_config_apply_value_missing_mut_param_2026-07-17 — test_config.spl: apply_test_config_value mutates its own stack frame only, never the caller's TestConfig

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_config_apply_value_missing_mut_param_2026-07-17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/test_config_apply_value_missing_mut_param_2026-07-17.md); `src/lib/nogc_sync_mut/test_runner/test_config.spl:218-252,258-280`
- Review rationale: Full report diagnoses discarded by-value TestConfig mutation. Current code replaces that helper boundary with test_config_resolve constructing and returning every field from layered entries; load path preserves intentional defaults-only early return. This is a source-level remedy to the discarded mutation, not permission to enable config loading. No current runtime verification.
- Review corrections: structural_change: yes -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> fixed_pending_verification; independent target review; historical execution is not a current receipt.

## test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17 — bin/simple test pays ~310s fixed setup per invocation; directory targets rejected, capping

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md); `src/app/test_daemon/light_daemon.spl:184-189`
- Review rationale: Full report separates measured setup cost from hang and records compiled-test spawn attempt was slower/reverted. Current daemon still spawns run source runner at184-189, corroborating load cost path. Cached artifact/graph remedy has not been validated; historical seed walltimes do not establish present pure-Simple performance or a known repair.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## test_runner_fixed_session_cost_2026-08-21 — `simple test <dir>` pays ~400s of fixed cost before running any test

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_fixed_session_cost_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/test_runner_fixed_session_cost_2026-08-21.md); `src/compiler/99.loader/compiler_sffi.spl:16-41`
- Review rationale: Full report plus entire current compiler_sffi compatibility module confirm duplicate CompilerContext/TypeInfo declarations replaced by reexports. Report explicitly leaves wider CudaModule/global-name collision and whole-module fallback unresolved. Removing two collisions is not a solution to directory fixed cost; current timing and module-local binding mechanism remain unknown.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## test_runner_process_limit_overflow_2026_10_12 — Test runner accepts overflowing process limit

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/test_runner/args_process_limit_boundary_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/app/test_runner/args_process_limit_boundary_spec.spl); `src/lib/nogc_sync_mut/test_runner/resource_policy.spl:7-25`; `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:147-148,171-175`
- Review rationale: Read entire boundary spec and actual validation wiring for both --max-procs spellings. Current guard rejects nondigits and significant decimal length/value above signedMAX before conversion, preserving zero and leading zeros. Explicit-end slice is an acknowledged workaround for a separate compiler defect, not evidence that slice defect is fixed. Process-limit source remedy exists; current executable untested.

## test_tree_divergence_982_diagnosis_2026-08-08 — check-test-tree-divergence reports 982 diverged (1 new, 1 stale-baselined) against baselin

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-test-tree-divergence.shs](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-test-tree-divergence.shs); `doc/08_tracking/bug/test_tree_divergence_982_diagnosis_2026-08-08.md`; `scripts/check/check-test-tree-divergence.shs:493-499,529-539,571-575,672-673`
- Review rationale: Recovered full diagnosis report; current guard compares canonical/shadow and now separately records mirror-only files before baseline set differences. This addresses one old wording/scope blind spot but not independent content divergence. Historical982 is not a current census and pairwise content reconciliation remains unknown; neither baseline regeneration nor deleting tests is a supported repair.
- Review corrections: validity: uncertain -> valid; independent target review; historical execution is not a current receipt.

## test_whole_cli_scope_provenance_2026_10_12 — Whole test CLI omits documentation scope provenance

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/test_runner/whole_scope_cli_spec.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/app/test_runner/whole_scope_cli_spec.spl); `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl:404-408,742`; `src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:178-188`
- Review rationale: Read all six real parser/scope regressions and actual --whole branch plus TestOptions construction. Flag sets whole=true independently of --all, is carried in returned options, and doctest scope selector returns repository scope when whole. Source remedy matches reported provenance loss; historical diagnostic pass does not qualify current whole/native execution.

## text_advanced_case_conversions_broken_by_char_index_arithmetic_2026-08-11 — BUG: text_advanced case conversions corrupted by `ch[0] ± 32` char arithmetic

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_advanced_case_conversions_broken_by_char_index_arithmetic_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/text_advanced_case_conversions_broken_by_char_index_arithmetic_2026-08-11.md); `src/lib/common/text_advanced.spl:23,175-185,208-212,236-239`
- Review rationale: Full report including resolved appendices and runner-zero-results caveat read. Current title/snake/camel implementations use char_code +/-32 then char_from_code, with import restored. Concrete source remedy exists for text arithmetic corruption; historical interpreter probes are not present runtime verification and separate Unicode indexing issue is not solved here.
- Review corrections: structural_change: yes -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> fixed_pending_verification; independent target review; historical execution is not a current receipt.

## text_len_substring_bytes_but_index_chars_2026-08-30 — `text.len()`/`substring` are byte-indexed but `text[i]` is char-indexed

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_len_substring_bytes_but_index_chars_2026-08-30.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/text_len_substring_bytes_but_index_chars_2026-08-30.md); `src/app/llm_caret/redact.spl:85-111`; `src/runtime/runtime_native.c:4251-4254,4438`; `src/runtime/runtime.c:625-631`
- Review rationale: Full report plus current caret scanners confirm all four bound by len while indexing text. Current native rt_string_len returns byte length; core C spl_str_index_char is itself byte indexed, while historical interpreter report and native char_code_at use character units. This is an implementation/contract divergence, not universally identical behavior. Choosing language semantics and auditing scanners is unresolved; no known root fix.
- Review corrections: structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; independent target review; historical execution is not a current receipt.

## text_literal_brace_run_swallows_following_concatenation_2026-09-05 — A non-parseable `{...}` interpolation body silently falls back to literal text, swallowing an enclosed `+` concatenation

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_literal_brace_run_swallows_following_concatenation_2026-09-05.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/text_literal_brace_run_swallows_following_concatenation_2026-09-05.md); `src/compiler_rust/parser/src/lexer/strings.rs:271-294,340-365,533-560`
- Review rationale: Full report distinguishes parenthesized open-brace concatenation from valid nested strings. Current lexer guards top-level quotes only at paren_depth==0 and tracks nested string state; report trigger has parenthesis depth and is not settled by that sibling repair. Full parser fallback/error compatibility still needs design before known fix; cut pipeline is only workaround.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## text_literal_to_i64_returns_rodata_pointer_native_2026-09-07 — `"7".to_i64()` returns a `.rodata` pointer under native codegen (2026-09-07)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_literal_to_i64_returns_rodata_pointer_native_2026-09-07.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/text_literal_to_i64_returns_rodata_pointer_native_2026-09-07.md); `src/runtime/runtime_native.c:7411-7463`
- Review rationale: Full report plus current runtime confirm rt_to_int_dynamic returns non-registry-string value unchanged, while rt_string_to_int_any normalizes text buffers. That preserves numeric identity and explains why pointer heuristics are unsafe. Current typed literal lowering route and optional-parse contract have not been traced, so do not call substituting the global total-parse helper a complete known remedy.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; inspection_level: report_reviewed -> source_reviewed; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## text_method_arg_copied_through_extern_abi_per_call_2026-10-25 — text method arg copied through extern abi per call (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_method_arg_copied_through_extern_abi_per_call_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/text_method_arg_copied_through_extern_abi_per_call_2026-10-25.md); `src/compiler/80.driver/driver_entry_closure_core.spl:621-639`
- Review rationale: Full measured ABI-copy report and entire current _driver_line_end inspected. Forward byte_at scan removes that per-line fulltext-copy hot site and handles newline absence; it does not repair extern receiver ownership/copy lowering or sibling index_of/contains sites. Keep root solution and structural scope unknown, current performance untested.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.

## text_slice_omitted_end_native_contract_2026_10_12 — Colon omitted-end text slice returns empty in native legacy provider

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; review state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/text_slice_omitted_end_native_contract_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/text_slice_omitted_end_native_contract_2026_10_12.md); `src/compiler/10.frontend/core/compiler/cg_expr.spl:790-794`; `src/runtime/runtime_legacy_core.c:283-294`
- Review rationale: Full report plus actual cg_slice_expr and legacy provider inspected: generated colon call forwards end unchanged; provider clamps negative end to start. Candidate projection is external/unqualified and shared text.slice ABI forbids blind runtime change. Need actual hygienic colon-only owner fix preserving once/order evaluation and a source-containing generation; explicit-end process validator workaround is not closure.
- Review corrections: solution: known -> unknown; structural_change: yes -> unknown; recommended_action: fix_candidate -> keep_open; independent target review; historical execution is not a current receipt.
