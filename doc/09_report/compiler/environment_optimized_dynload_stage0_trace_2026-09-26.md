# Dynload Stage 0 production caller trace

**Source snapshot:** `2a72cb59544f475a24ed60bb6852970042ec766e` (2026-09-26).
This is source evidence for Stage 0 of
`doc/03_plan/compiler/environment_optimized_dynamic_libraries.md`, not a
runtime qualification or a completed parser provider.

## Parser entrypoints and provider seams

| Production path | Source call chain | Current provider result |
|---|---|---|
| Native build driver | `src/compiler/80.driver/driver_source_pipeline_parsing.spl` calls `parse_full_frontend_with_advisory_policy_v1`; `src/compiler/10.frontend/frontend.spl` calls `frontend_parse_or_restore`, then `parse_and_build_module_scoped` on a cache miss; `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` calls `parse_module_body`. | The driver executes the flat-AST legacy parser. The advisory provider is a preprocessing decision; it does not replace the grammar/action parser. A cache hit may skip parsing altogether, so differential runs must disable or account for that cache. |
| Core compiler and interpreter | `src/compiler/10.frontend/core/compiler/driver.spl` and `src/compiler/10.frontend/core/interpreter/{mod,module_loader_core,module_loader_lazy}.spl` call `core_frontend_parse_{reset,append,isolated}` in `src/compiler/10.frontend/core/frontend.spl`. | `parser_provider_v1_default` selects `LegacyReference`; admission rejects all candidates. This facade is separate from the native build driver's flat-AST bridge. |
| Parse-result seam | `src/compiler/80.driver/parse_result_provider_seam_v1.spl` defines `ParseResultProviderV1`, a scalar slot, a refusing SIMD slot, normalization, and dialect identities. Its scalar callable itself invokes `parse_and_build_module_scoped`. A search of `src/**/*.spl` found no call to `parse_result_seam_request_v1` or `parse_result_provider_scalar_v1` outside their definitions. | The seam is not wired into the production driver and its scalar slot is the same legacy flat-AST implementation. Comparing it with the flat-AST parser would be a self-comparison, not independent canonical parity. |

`src/lib/common/structural/parse/parse_cpu_reference.spl` executes a lexical
DFA. `src/lib/common/structural/parse/dialect.spl` declares grammar and action
program shapes, but this snapshot has no executed canonical Simple grammar and
action program behind either production entrypoint. The four-case manifest in
`src/compiler/10.frontend/core/frontend.spl` correctly reports its candidate
prerequisite unavailable.

## Environment, loader, and queue consumers

| Contract | Source evidence | Stage 0 classification |
|---|---|---|
| Feature model and host probe | `src/compiler/80.driver/host_environment_snapshot_v1.spl` imports the shared feature registry and `std.sffi.host` CPUID/OS-state facts; `src/compiler/80.driver/x86_variant_admission_v1.spl` checks required CPU features. | Implemented admission components; no proof here that a full parser variant executes. |
| Composition generation | `src/compiler/80.driver/environment_variant_composite_publication_v1.spl` calls `binding_runtime_publish_plan_v1`; `src/lib/nogc_sync_mut/composition/environment_variants/binding_runtime_v1.spl` owns the active plan. | Implemented publication path; parser frontend binding remains unwired. |
| Parser variant planner | `src/compiler/80.driver/parser_variant_build_plan_v1.spl` defines the planner. A search of `src/**/*.spl` found no production call to `parser_variant_build_plan_v1`. | Scaffold, not a built sibling. |
| SIMD lexical loader | `src/compiler/99.loader/parser_structural_package_owner_v1.spl` owns a retained lexical-mask scope; `parser_structural_guarded_scope_v1.spl` calls the native mask function. No call from `src/compiler/80.driver`, `src/compiler/10.frontend`, or `src/app` reaches that package in this snapshot. | A guarded lexical primitive, not an admitted full parser. |
| GPU parse gate | `src/compiler/80.driver/driver_source_pipeline_parsing.spl` consumes `FRONTEND_OFFLOAD_GPU_PARSE_AVAILABLE` from `src/compiler/00.common/structural_contracts/frontend_offload_switch.spl`; the constant is false. | GPU grammar provider unavailable. |
| Packed draw queue | `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` advances through `engine2d_host_gpu_runtime_complete_pending` with `engine2d_gpu_device_evidence_none()`. | Host completion is not device execution proof and does not qualify the parser GPU path. |

## Next integration unit

Route a *distinct* canonical scalar Simple grammar/action engine through one
frontend provider boundary shared by the native build driver and core
compiler/interpreter. Preserve the existing flat-AST and core legacy paths as
oracles. The differential runner must capture reset, append, isolated errors,
tokens, regions, AST/HIR actions, source mappings, diagnostics, invalidation,
and a deterministic digest on each path, with cache behavior controlled. Only
then can the scalar provider be admitted; SIMD, GPU, and dynlib variants inherit
the same semantic contract.

## Evidence still required for Stage 0 exit

The selected dynload requirements already exist, but this report does not
provide a source-matched pure-Simple runner, reproducible build/test baseline,
CPU-only startup latency and max RSS, representative parser workload timings,
mapped-text measurements, or device-path negative controls. The current macOS
bootstrap attempt stops at the Cocoa runtime ownership gate; that separate
blocker is recorded in
`doc/08_tracking/bug/macos_cocoa_runtime_dylib_missing_bootstrap_authority_2026-09-22.md`.
