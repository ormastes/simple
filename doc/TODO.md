# TODO Tracking

**Total:** 199 items | **Open:** 193 | **Blocked:** 6

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 2 |
| P1 | 9 |
| P2 | 37 |
| P3 | 151 |

## By Area

| Area | Count |
|------|-------|
| sspec-verification | 1 |
| llm-caret-messaging | 1 |
| sspec | 1 |
| llm-caret | 3 |
| test | 2 |
| general | 150 |
| sspec-live-capture | 1 |
| uno_q | 1 |
| rendering | 1 |
| gpu | 30 |
| compiler-resolver | 2 |
| llm-caret-server | 1 |
| debug | 1 |
| cosmos | 1 |
| spipe_docgen | 1 |
| infra | 1 |
| driver | 1 |

## P0 Critical

- [TODO] **POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured.** - `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md:19`
- [TODO] **BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command.** - `doc/03_plan/sys_test/render_lane_mission_showcase.md:53`

## P1 High Priority

- [TODO] `probe` is not a probe. It queries no device: it is a - `src/lib/gc_async_mut/gpu/session/graphics_capabilities.spl:30`
- [TODO] NO Metal device evidence exists on this machine, so no - `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl:75`
- [TODO] Remove this rename workaround once the seed resolves bare names by import scope instead of a global registry: a function's own parameter must win over a same-named imported module (doc/08_tracking/bug/module_name_shadows_function_parameter_2026-09-06.md) - `src/lib/nogc_sync_mut/http_server/server.spl:219`
- [TODO] SffiHttpMethod/SffiHttpResponse/SffiHttpStatus are named apart from http_server's HttpMethod/HttpResponse/HttpStatus only because the seed resolves type and enum-variant names globally by bare name; restore the plain names once resolution is import-scoped (doc/08_tracking/bug/enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06.md) - `src/lib/nogc_sync_mut/io/http_sffi.spl:122`
- [TODO] Reports every live agent as exited on the shipped binary: the seed's rt_process_is_running returns false for any pid it did not spawn and a tmux pane is tmux's child; fixed in source, needs the deploy (doc/08_tracking/bug/interpreter_process_is_running_false_for_unspawned_pid_2026-09-06.md) - `src/app/llm_caret/cs_dashboard.spl:269`
- [TODO] Verify Stage 3 self-hosting: the bootstrap has only ever reached "Stage 2 admitted", and Stage 3 -- stage2 recompiling THIS file -- has never been attempted, so the byte-identical stage2 == stage3 fixpoint that the bootstrap claim rests on is unproven; see doc/08_tracking/bug/bootstrap_stage2_admission_refused_by_concurrent_source_edits_2026-09-05.md - `src/app/cli/bootstrap_main.spl:6`
- [TODO] T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it - `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl:48`
- [TODO] Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance - `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:110`
- [TODO] Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary - `doc/08_tracking/todo/gpu_scheduler_specs_need_selfhosted_rerun_2026-09-06.md:1`

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | wire up hwprobe when available | `src/compiler/30.types/simd_capabilities.spl` | 492 |
| 1 | TODO | general | P3 | promote this to self.error_fatal (with an Unreachable MIR | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 2944 |
| 2 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/system_api.spl` | 130 |
| 3 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/semihost_transport.spl` | 307 |
| 4 | TODO | gpu | P1 | `probe` is not a probe. It queries no device: it is a | `src/lib/gc_async_mut/gpu/session/graphics_capabilities.spl` | 30 |
| 5 | TODO | gpu | P2 | report distinct submit/gpu_finished/complete/retire phases once a per-submission completion callback exists; the tree has no such Vulkan extern today | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 61 |
| 6 | TODO | gpu | P2 | set fence_token_available once rt_vulkan_create_fence / rt_vulkan_wait_fence land; submit_and_wait() blocks and returns no fence handle | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 63 |
| 7 | TODO | gpu | P2 | set device_timestamps_available once rt_vulkan_create_query_pool / rt_vulkan_get_query_results land; never fabricate device ticks | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 65 |
| 8 | TODO | gpu | P1 | NO Metal device evidence exists on this machine, so no | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 75 |
| 9 | TODO | gpu | P2 | verify this probe against a host where metal_available() is true; on an Apple M4 under the 2026-09-05 bootstrap seed it returns false (Vulkan/MoltenVK reports the same device as "Apple M4"), so the Metal branch below is unexercised | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 83 |
| 10 | TODO | gpu | P2 | report distinct submit/gpu_finished/complete/retire phases once an addCompletedHandler-backed extern exists; metal_sffi_run_compute_frame collapses submit and completion | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 106 |
| 11 | TODO | gpu | P2 | set fence_token_available once rt_metal_command_buffer_event / shared-event externs land; metal_wait() blocks and returns no token | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 108 |
| 12 | TODO | gpu | P2 | set device_timestamps_available once MTLCounterSampleBuffer externs land; never fabricate device ticks | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 110 |
| 13 | TODO | gpu | P2 | D3D12 provider does not exist in this tree; add rt_d3d12_* externs before claiming a D3D12 conformance lane | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 120 |
| 14 | TODO | gpu | P2 | DirectX has NO GPU text on either platform: both | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 121 |
| 15 | TODO | gpu | P2 | report distinct submit/gpu_finished/complete/retire phases once a D3D11 event-query extern exists; rt_directx_execute_readback_checked collapses submit and readback | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 143 |
| 16 | TODO | gpu | P2 | set fence_token_available once rt_directx_create_fence / rt_directx_wait_fence land | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 145 |
| 17 | TODO | gpu | P2 | set device_timestamps_available once D3D11 timestamp-query externs land; never fabricate device ticks | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 147 |
| 18 | TODO | gpu | P2 | The contract evaluated above can be reported UNMET by a | `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` | 823 |
| 19 | TODO | gpu | P2 | When a VkQueryPool timestamp extern exists it must supply | `src/lib/gc_async_mut/gpu/engine2d/vulkan_resident_2d.spl` | 724 |
| 20 | TODO | gpu | P2 | BLOCKED ON BOOTSTRAP. The freestanding `ud2` / | `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | 613 |
| 21 | TODO | gpu | P2 | No software/CPU dispatch rung exists. `software_backend` | `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | 626 |
| 22 | TODO | general | P3 | (gpu) model shared-memory exchange and a real gpu_syncthreads barrier in this | `src/lib/gc_async_mut/gpu_ops.spl` | 462 |
| 23 | TODO | compiler-resolver | P1 | Remove this rename workaround once the seed resolves bare names by import scope instead of a global registry: a function's own parameter must win over a same-named imported module (doc/08_tracking/bug/module_name_shadows_function_parameter_2026-09-06.md) | `src/lib/nogc_sync_mut/http_server/server.spl` | 219 |
| 24 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 25 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 26 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 27 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 28 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 29 | TODO | compiler-resolver | P1 | SffiHttpMethod/SffiHttpResponse/SffiHttpStatus are named apart from http_server's HttpMethod/HttpResponse/HttpStatus only because the seed resolves type and enum-variant names globally by bare name; restore the plain names once resolution is import-scoped (doc/08_tracking/bug/enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06.md) | `src/lib/nogc_sync_mut/io/http_sffi.spl` | 122 |
| 30 | TODO | general | P3 | (gpu) expose cudaMemcpyPeer / cuMemcpyPeer so multi-GPU transfers do not have | `src/lib/nogc_sync_mut/io/cuda_sffi.spl` | 151 |
| 31 | TODO | general | P3 | (sosix C3) prove the zero-wrapper lowering once native-build works on this | `src/lib/nogc_async_mut/sosix/posix.spl` | 19 |
| 32 | TODO | general | P3 | (sosix C4) replace this reference provider with a Linux io_uring provider | `src/lib/nogc_async_mut/sosix/file_driver.spl` | 13 |
| 33 | TODO | general | P3 | (sosix C5) add the macOS and Windows providers on a host that has them; this | `src/lib/nogc_async_mut/sosix/file_driver.spl` | 16 |
| 34 | TODO | gpu | P2 | with a real device attached, replace engine2d_gpu_device_evidence_none() here with provider evidence (binary identity, device name, driver identity, monotonic host submit/complete ns, negative control) and advance through ENGINE2D_GPU_PHASE_GPU_FINISHED so device_execution_proven can legitimately flip true | `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` | 362 |
| 35 | TODO | gpu | P2 | with a real device attached, verify the arena named by the payload lease is only released after the device has signalled it is done with it; the compatibility provider has no fence, so this drain cannot prove that today | `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` | 417 |
| 36 | TODO | general | P3 | Implement ValueBuilder and complete handler integration | `src/compiler_rust/lib/std/src/sdn/handler.spl` | 205 |
| 37 | TODO | general | P3 | add more about copy-paste and human readability. | `src/compiler_rust/vendor/shlex/src/quoting_warning.md` | 365 |
| 38 | TODO | general | P3 | (sosix G3) retire this route onto the v1 positioned stack once the QEMU | `src/os/sosix/io_rw.spl` | 14 |
| 39 | TODO | general | P3 | when netstack is wired, call net_service_poll() here to drive | `src/os/kernel/net/driver_shim.spl` | 337 |
| 40 | TODO | llm-caret-server | P2 | The whole SSE body is built and returned at once; real SDK streaming wants chunked token-by-token delivery. Frame shapes are already correct, so this is a transport change, not a format one | `src/app/llm_caret/server.spl` | 226 |
| 41 | TODO | llm-caret | P1 | Reports every live agent as exited on the shipped binary: the seed's rt_process_is_running returns false for any pid it did not spawn and a tmux pane is tmux's child; fixed in source, needs the deploy (doc/08_tracking/bug/interpreter_process_is_running_false_for_unspawned_pid_2026-09-06.md) | `src/app/llm_caret/cs_dashboard.spl` | 269 |
| 42 | TODO | llm-caret | P2 | Delete this EOF ceiling once the fixed seed ships; same workaround as chat_tui.spl and obsolete for the same reason | `src/app/llm_caret/cs_main.spl` | 35 |
| 43 | TODO | llm-caret | P2 | Delete this EOF ceiling and rely on the loop's existing nil branch once the fixed seed ships; removing it earlier breaks caret on the current binary (doc/08_tracking/bug/seed_interpreter_stdin_read_line_erases_eof_2026-09-06.md) | `src/app/llm_caret/chat_tui.spl` | 745 |
| 44 | TODO | debug | P2 | system-level acceptance spec for `simple debug write <root> --build-id ... <artifact>...` followed by `simple debug inspect <root>` through the real CLI; AC-4 of .spipe/debug_evidence_bundle_writer_wave2 is verified by hand only | `src/app/cli_debug/evidence_write_v1.spl` | 20 |
| 45 | TODO | driver | P1 | Verify Stage 3 self-hosting: the bootstrap has only ever reached "Stage 2 admitted", and Stage 3 -- stage2 recompiling THIS file -- has never been attempted, so the byte-identical stage2 == stage3 fixpoint that the bootstrap claim rests on is unproven; see doc/08_tracking/bug/bootstrap_stage2_admission_refused_by_concurrent_source_edits_2026-09-05.md | `src/app/cli/bootstrap_main.spl` | 6 |
| 46 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/03_system/generated/spec_matchers_spec.spl` | 115 |
| 47 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/03_system/feature/usage/trait_coherence_spec.spl` | 381 |
| 48 | TODO | general | P3 | Lambda default parameters not yet supported | `test/03_system/feature/usage/parser_default_keyword_spec.spl` | 189 |
| 49 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 50 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 89 |
| 51 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 103 |
| 52 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 110 |
| 53 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 83 |
| 54 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 87 |
| 55 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 91 |
| 56 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 66 |
| 57 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 70 |
| 58 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 81 |
| 59 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 85 |
| 60 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1052 |
| 61 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1057 |
| 62 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1062 |
| 63 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1067 |
| 64 | TODO | sspec-live-capture | P2 | ML live-capture (T2g) blocked: libtorch unavailable, rt_torch_available() returns false. When it returns true, write live_ml_capture_spec.spl per live_audio_capture_spec.spl | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 33 |
| 65 | TODO | sspec-verification | P1 | T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 48 |
| 66 | TODO | llm-caret-messaging | P1 | Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance | `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl` | 110 |
| 67 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 68 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 69 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 70 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 71 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 72 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 73 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 74 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 75 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 76 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/feature/usage/set_literal_spec.spl` | 57 |
| 77 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/feature/usage/set_literal_spec.spl` | 98 |
| 78 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 107 |
| 79 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 116 |
| 80 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 141 |
| 81 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 158 |
| 82 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/feature/usage/primitive_types_spec.spl` | 84 |
| 83 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/feature/usage/macro_validation_spec.spl` | 206 |
| 84 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/feature/usage/trait_coherence_spec.spl` | 365 |
| 85 | TODO | general | P3 | Lambda default parameters not yet supported | `test/feature/usage/parser_default_keyword_spec.spl` | 172 |
| 86 | TODO | general | P3 | Execute binary and wait for completion | `test/perf/native_layout_performance_spec.spl` | 46 |
| 87 | TODO | general | P3 | Parse output from time -v or perf stat | `test/perf/native_layout_performance_spec.spl` | 60 |
| 88 | TODO | general | P3 | Compile source | `test/perf/native_layout_performance_spec.spl` | 69 |
| 89 | TODO | general | P3 | Use file stats | `test/perf/native_layout_performance_spec.spl` | 88 |
| 90 | TODO | general | P3 | Compile both versions | `test/perf/native_layout_performance_spec.spl` | 141 |
| 91 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 172 |
| 92 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 201 |
| 93 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 233 |
| 94 | TODO | general | P3 | Compile both and compare | `test/perf/native_layout_performance_spec.spl` | 267 |
| 95 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/perf/native_layout_performance_spec.spl` | 341 |
| 96 | TODO | general | P3 | Benchmark actual execution | `test/perf/native_layout_performance_spec.spl` | 368 |
| 97 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/perf/intensive/http/h3_settings_write_frame_spec.spl` | 13 |
| 98 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/system/generated/spec_matchers_spec.spl` | 63 |
| 99 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 64 |
| 100 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 68 |
| 101 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 72 |
| 102 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_module_spec.spl` | 10 |
| 103 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 104 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_types_spec.spl` | 10 |
| 105 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 106 | TODO | sspec | P2 | convert to real execution. This scenario text-pins the | `test/01_unit/compiler/backend_plugin/dynamic_loader_spec.spl` | 63 |
| 107 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/parser_spec.spl` | 209 |
| 108 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 335 |
| 109 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/jit_context_spec.spl` | 387 |
| 110 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/jit_context_spec.spl` | 396 |
| 111 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/jit_context_spec.spl` | 400 |
| 112 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 404 |
| 113 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 408 |
| 114 | TODO | gpu | P2 | No spec asserts a SUCCESSFUL Vulkan window present. | `test/01_unit/lib/gpu/engine2d/vulkan_session_release_identity_spec.spl` | 50 |
| 115 | TODO | gpu | P2 | No Vulkan shutdown/leak spec exists. This file proves the | `test/01_unit/lib/gpu/engine2d/vulkan_session_release_identity_spec.spl` | 56 |
| 116 | TODO | gpu | P2 | No mask-plane spec exists anywhere in test/. The engine2d | `test/01_unit/lib/gpu/engine2d/vulkan_session_release_identity_spec.spl` | 62 |
| 117 | TODO | gpu | P2 | Engine2D.software_backend hands back a DETACHED copy of the | `test/01_unit/lib/gpu/engine2d/engine_software_lane_contract_spec.spl` | 58 |
| 118 | TODO | gpu | P2 | The whole src/lib/gc_async_mut/gpu/session/ layer is an | `test/01_unit/gpu/graphics_session_spec.spl` | 43 |
| 119 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 98 |
| 120 | TODO | general | P3 | Test function compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 105 |
| 121 | TODO | general | P3 | Test class compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 112 |
| 122 | TODO | general | P3 | Test enum compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 130 |
| 123 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 160 |
| 124 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 184 |
| 125 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 188 |
| 126 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 204 |
| 127 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 214 |
| 128 | TODO | general | P3 | Test recursive types | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 232 |
| 129 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 253 |
| 130 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 267 |
| 131 | TODO | general | P3 | Test import resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 291 |
| 132 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 298 |
| 133 | TODO | general | P3 | Test circular import detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 302 |
| 134 | TODO | general | P3 | Test hot reload | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 330 |
| 135 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 346 |
| 136 | TODO | general | P3 | Test cache eviction | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 355 |
| 137 | TODO | general | P3 | Test refcount management | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 359 |
| 138 | TODO | general | P3 | Test leak detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 363 |
| 139 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 140 | TODO | general | P3 | Implement actual ELF reading | `test/integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 141 | TODO | general | P3 | Implement actual symbol parsing | `test/integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 142 | TODO | general | P3 | Implement actual size measurement | `test/integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 143 | TODO | general | P3 | Verify function order in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 144 | TODO | general | P3 | Verify actual ordering in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 145 | TODO | general | P3 | Verify relocations are correct | `test/integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 146 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 147 | TODO | general | P3 | Create minimal MirModule and compile | `test/integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 148 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_module_spec.spl` | 10 |
| 149 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 150 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_types_spec.spl` | 10 |
| 151 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 152 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/unit/compiler/frontend/parser_spec.spl` | 69 |
| 153 | TODO | general | P3 | Create test template and type args | `test/unit/compiler/loader/jit_context_spec.spl` | 387 |
| 154 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/unit/compiler/loader/jit_context_spec.spl` | 396 |
| 155 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/unit/compiler/loader/jit_context_spec.spl` | 400 |
| 156 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 404 |
| 157 | TODO | general | P3 | Verify DI container passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 408 |
| 158 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/unit/sffi/sffi_public_api_spec.spl` | 131 |
| 159 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/native_layout_performance_spec.spl` | 52 |
| 160 | TODO | general | P3 | Compile source | `test/05_perf/native_layout_performance_spec.spl` | 131 |
| 161 | TODO | general | P3 | Use file stats | `test/05_perf/native_layout_performance_spec.spl` | 150 |
| 162 | TODO | general | P3 | Compile both versions | `test/05_perf/native_layout_performance_spec.spl` | 208 |
| 163 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 241 |
| 164 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 272 |
| 165 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 306 |
| 166 | TODO | general | P3 | Compile both and compare | `test/05_perf/native_layout_performance_spec.spl` | 342 |
| 167 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/native_layout_performance_spec.spl` | 422 |
| 168 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/native_layout_performance_spec.spl` | 451 |
| 169 | TODO | gpu | P2 | Exercise the DirectX provider probe on a Windows or DXVK host | `doc/08_tracking/todo/gpu_directx_provider_probe_never_exercised_2026-09-06.md` | 1 |
| 170 | TODO | general | P3 | admit SFFI providers with artifact-bound evidence | `doc/08_tracking/todo/sffi_v2_provider_admission_2026-08-27.md` | 1 |
| 171 | TODO | general | P3 | Environment variant frontend seam integration | `doc/08_tracking/todo/environment_optimized_dynamic_libraries_frontend_seam_2026-09-07.md` | 1 |
| 172 | TODO | general | P3 | hardening plan — resume after the bootstrap seed redeploy is stable | `doc/08_tracking/todo/hardening_resume_after_seed_redeploy_2026-08-25.md` | 1 |
| 173 | TODO | gpu | P2 | Exercise the Metal provider probe on a host where metal_available() is true | `doc/08_tracking/todo/gpu_metal_provider_probe_never_exercised_2026-09-06.md` | 1 |
| 174 | TODO | general | P3 | Complete x86 V2 environment producer migration and qualification | `doc/08_tracking/todo/environment_optimized_dynamic_libraries_x86_v2_migration_2026-09-11.md` | 1 |
| 175 | TODO | infra | P3 | Build the native HTTPServer benchmark gate scripts or drop the claim | `doc/08_tracking/todo/native_httpserver_benchmark_gate_scripts_missing_2026-08-08.md` | 20 |
| 176 | TODO | general | P3 | Route dynamic manifest passes to a real execution path | `doc/08_tracking/todo/optimizer_manifest_dynamic_pass_routing_2026-08-18.md` | 1 |
| 177 | TODO | spipe_docgen | P2 | Render per-cell `%%mode` lane badges in notebook spec manuals | `doc/08_tracking/todo/spipe_docgen_lane_badges_2026-08-08.md` | 7 |
| 178 | TODO | general | P3 | std.async.runtime cannot wake clock-based (timer/sleep) futures | `doc/08_tracking/todo/async_runtime_timer_wakeup_for_sleep_2026-08-17.md` | 1 |
| 179 | TODO | general | P3 | bind protected DBFS objects to production descriptor owners | `doc/08_tracking/todo/server_data_namespace_fd_binding_v1.md` | 1 |
| 180 | TODO | test | P2 | Build (or restore) the Jupyter full-server and notebook-exec E2E helpers | `doc/08_tracking/todo/jupyter_e2e_helper_scripts_missing_2026-08-08.md` | 17 |
| 181 | TODO | gpu | P2 | Promote a provider from routing_only to full once fences and phases exist | `doc/08_tracking/todo/gpu_no_provider_reaches_full_conformance_2026-09-06.md` | 1 |
| 182 | TODO | general | P3 | test_runner_execute -> composite -> gpu_lane eager imports cost ~40s of seed-interpreter load | `doc/08_tracking/todo/test_runner_execute_composite_gpu_eager_import_cost_2026-08-17.md` | 1 |
| 183 | TODO | test | P1 | Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary | `doc/08_tracking/todo/gpu_scheduler_specs_need_selfhosted_rerun_2026-09-06.md` | 1 |
| 184 | TODO | uno_q | P2 | POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 18 |
| 185 | TODO | cosmos | P0 | POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 19 |
| 186 | TODO | gpu | P2 | Make the resident-slice readback counter a real measurement or delete it | `doc/08_tracking/todo/gpu_resident_readback_counter_unmeasurable_2026-09-06.md` | 1 |
| 187 | TODO | general | P3 | SOSIX runtime unification — blocked rows (resume conditions) | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 1 |
| 188 | TODO | general | P3 | (sosix F1) land the GPU G1 proxy storage slice on a host with a real GPU and a deployed pure-Simple binary; resume via doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md lanes B/C | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 44 |
| 189 | TODO | general | P3 | (sosix AC-3b) prove the QEMU serial row with observed bytes once a pure-Simple compiler accepted by simple_binary_is_valid is deployed; publish via produce-sosix-qemu-native-pass-bundle.shs and import via collect-sosix-qemu-evidence.shs | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 46 |
| 190 | TODO | general | P3 | (sosix G4) implement the SimpleOS device-initiated queues GQ-001..012 after the GQ-001 native capability report on real hardware | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 48 |
| 191 | TODO | general | P3 | (sosix startup-ab) re-run check-startup-size-performance-audit.shs on a host where its Simple probe rows do not exit 127, and diff against doc/09_report/startup_size_performance_audit_2026-05-27.md | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 50 |
| 192 | TODO | general | P3 | (sosix A5) drop the one-line `export use` shims for aliased re-exports once the compiler accepts `export use ... as`; until then every shim in src/os/sosix/core re-exports without renaming | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 52 |
| 193 | TODO | general | P3 | (simpleorch container) BLOCKED — implement and prove the Linux OCI native-container provider with PODMAN as the default engine; unblock with `apt install podman uidmap` plus lifting `kernel.apparmor_restrict_unprivileged_userns`, or fall back to `usermod -aG docker` | `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md` | 1 |
| 194 | TODO | general | P3 | (simpleorch container-oci) implement RuntimeProviderV1 create/start/wait/stop/destroy/recover for the Linux OCI lane; blocked on host privilege above, resume command in this file | `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md` | 106 |
| 195 | TODO | general | P3 | (simpleorch container-evidence) flip the native-container receipts in test/02_integration/app/ci/pipeline_runner_spec.spl from VERDICT_BLOCKED to a real container receipt (attempt 1, run nonce in stdout) once the lane is unblocked | `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md` | 107 |
| 196 | TODO | general | P3 | Environment-Optimized Dynamic Libraries self-hosted evidence | `doc/08_tracking/todo/environment_optimized_dynamic_libraries_selfhost_evidence_2026-09-07.md` | 1 |
| 197 | TODO | gpu | P2 | Qualify Vulkan resident-2D device evidence with real timestamps and uploaded rows | `doc/08_tracking/todo/gpu_resident_vulkan_device_evidence_unqualified_2026-09-06.md` | 1 |
| 198 | TODO | rendering | P0 | BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command. | `doc/03_plan/sys_test/render_lane_mission_showcase.md` | 53 |
