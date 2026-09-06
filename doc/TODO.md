# TODO Tracking

**Total:** 290 items | **Open:** 287 | **Blocked:** 3

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 2 |
| P1 | 4 |
| P2 | 27 |
| P3 | 257 |

## By Area

| Area | Count |
|------|-------|
| sspec-verification | 1 |
| llm-caret-messaging | 1 |
| test | 2 |
| general | 256 |
| sspec-live-capture | 1 |
| rendering | 1 |
| uno_q | 1 |
| gpu | 20 |
| cosmos | 1 |
| sspec-maintain | 1 |
| bootstrap | 1 |
| ui | 2 |
| spipe_docgen | 1 |
| infra | 1 |

## P0 Critical

- [TODO] **BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command.** - `doc/03_plan/sys_test/render_lane_mission_showcase.md:53`
- [TODO] **POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured.** - `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md:17`

## P1 High Priority

- [TODO] T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it - `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl:48`
- [TODO] Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance - `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:110`
- [TODO] Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary - `doc/08_tracking/todo/gpu_scheduler_specs_need_selfhosted_rerun_2026-09-06.md:1`
- [TODO] Enhance scoring rules to recognize lane-gated notebook specs - `doc/08_tracking/todo/sspec_maintain_lane_aware_scoring_2026-08-08.md:5`

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `src/app/devhub/cmd_daily_debug.spl` | 165 |
| 1 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `src/app/itf/cmd_daily_debug.spl` | 159 |
| 2 | TODO | general | P3 | Import bugdb handlers when available | `src/app/mcp/bootstrap/main_optimized.spl` | 244 |
| 3 | TODO | general | P3 | url_encode should percent-encode each UTF-8 BYTE (%C3%A9), not | `src/compiler_rust/lib/std/src/tooling/url_utils.spl` | 125 |
| 4 | TODO | general | P3 | Implement ValueBuilder and complete handler integration | `src/compiler_rust/lib/std/src/sdn/handler.spl` | 205 |
| 5 | TODO | general | P3 | add more about copy-paste and human readability. | `src/compiler_rust/vendor/shlex/src/quoting_warning.md` | 365 |
| 6 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `src/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 7 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 8 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 9 | TODO | gpu | P2 | report distinct submit/gpu_finished/complete/retire phases once a per-submission completion callback exists; the tree has no such Vulkan extern today | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 61 |
| 10 | TODO | gpu | P2 | set fence_token_available once rt_vulkan_create_fence / rt_vulkan_wait_fence land; submit_and_wait() blocks and returns no fence handle | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 63 |
| 11 | TODO | gpu | P2 | set device_timestamps_available once rt_vulkan_create_query_pool / rt_vulkan_get_query_results land; never fabricate device ticks | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 65 |
| 12 | TODO | gpu | P2 | verify this probe against a host where metal_available() is true; on an Apple M4 under the 2026-09-05 bootstrap seed it returns false (Vulkan/MoltenVK reports the same device as "Apple M4"), so the Metal branch below is unexercised | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 74 |
| 13 | TODO | gpu | P2 | report distinct submit/gpu_finished/complete/retire phases once an addCompletedHandler-backed extern exists; metal_sffi_run_compute_frame collapses submit and completion | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 97 |
| 14 | TODO | gpu | P2 | set fence_token_available once rt_metal_command_buffer_event / shared-event externs land; metal_wait() blocks and returns no token | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 99 |
| 15 | TODO | gpu | P2 | set device_timestamps_available once MTLCounterSampleBuffer externs land; never fabricate device ticks | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 101 |
| 16 | TODO | gpu | P2 | D3D12 provider does not exist in this tree; add rt_d3d12_* externs before claiming a D3D12 conformance lane | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 111 |
| 17 | TODO | gpu | P2 | report distinct submit/gpu_finished/complete/retire phases once a D3D11 event-query extern exists; rt_directx_execute_readback_checked collapses submit and readback | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 126 |
| 18 | TODO | gpu | P2 | set fence_token_available once rt_directx_create_fence / rt_directx_wait_fence land | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 128 |
| 19 | TODO | gpu | P2 | set device_timestamps_available once D3D11 timestamp-query externs land; never fabricate device ticks | `src/lib/gc_async_mut/gpu/engine2d/gpu_provider_probes.spl` | 130 |
| 20 | TODO | gpu | P2 | When a VkQueryPool timestamp extern exists it must supply | `src/lib/gc_async_mut/gpu/engine2d/vulkan_resident_2d.spl` | 281 |
| 21 | TODO | gpu | P2 | upload the sealed packed rows into a device buffer per frame and count the real bytes here | `src/lib/gc_async_mut/gpu/engine2d/vulkan_resident_2d.spl` | 375 |
| 22 | TODO | general | P3 | (gpu) model shared-memory exchange and a real gpu_syncthreads barrier in this | `src/lib/gc_async_mut/gpu_ops.spl` | 462 |
| 23 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/system_api.spl` | 130 |
| 24 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/semihost_transport.spl` | 307 |
| 25 | TODO | general | P3 | (gpu) expose cudaMemcpyPeer / cuMemcpyPeer so multi-GPU transfers do not have | `src/lib/nogc_sync_mut/io/cuda_sffi.spl` | 151 |
| 26 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 27 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 28 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 29 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 30 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 31 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 32 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 33 | TODO | ui | P2 | vbox does not honour the `flex` prop at all — it counts children | `src/lib/common/ui/layout.spl` | 123 |
| 34 | TODO | ui | P2 | these accessors return LOGICAL units, but layout_vbox/layout_hbox | `src/lib/common/ui/layout.spl` | 429 |
| 35 | TODO | general | P3 | (sosix C4) replace this reference provider with a Linux io_uring provider | `src/lib/nogc_async_mut/sosix/file_driver.spl` | 13 |
| 36 | TODO | general | P3 | (sosix C5) add the macOS and Windows providers on a host that has them; this | `src/lib/nogc_async_mut/sosix/file_driver.spl` | 16 |
| 37 | TODO | general | P3 | (sosix C3) prove the zero-wrapper lowering once native-build works on this | `src/lib/nogc_async_mut/sosix/posix.spl` | 19 |
| 38 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `src/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 39 | TODO | gpu | P2 | with a real device attached, replace engine2d_gpu_device_evidence_none() here with provider evidence (binary identity, device name, driver identity, monotonic host submit/complete ns, negative control) and advance through ENGINE2D_GPU_PHASE_GPU_FINISHED so device_execution_proven can legitimately flip true | `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` | 352 |
| 40 | TODO | gpu | P2 | with a real device attached, verify the arena named by the payload lease is only released after the device has signalled it is done with it; the compatibility provider has no fence, so this drain cannot prove that today | `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl` | 369 |
| 41 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 42 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 43 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 44 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 45 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 46 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 47 | TODO | general | P3 | (sosix G3) retire this route onto the v1 positioned stack once the QEMU | `src/os/sosix/io_rw.spl` | 14 |
| 48 | TODO | general | P3 | when netstack is wired, call net_service_poll() here to drive | `src/os/kernel/net/driver_shim.spl` | 337 |
| 49 | TODO | general | P3 | `has_current_lines` is an unresolved name (porter artifact); it is | `src/compiler/90.tools/text_diff.spl` | 102 |
| 50 | TODO | general | P3 | wire up hwprobe when available | `src/compiler/30.types/simd_capabilities.spl` | 416 |
| 51 | TODO | general | P3 | promote this to self.error_fatal (with an Unreachable MIR | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 2858 |
| 52 | TODO | general | P3 | this arm is an incomplete port. The Rust original | `src/compiler/35.semantics/macro_contracts.spl` | 111 |
| 53 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `src/compiler/80.driver/watcher/watcher_daemon.spl` | 73 |
| 54 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 51 |
| 55 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 58 |
| 56 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 67 |
| 57 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 74 |
| 58 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 83 |
| 59 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 90 |
| 60 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 118 |
| 61 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 127 |
| 62 | TODO | general | P3 | Simulate write failure | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 134 |
| 63 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 143 |
| 64 | TODO | general | P3 | Implement after process spawning is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 152 |
| 65 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/unit/app/tooling/test_db_integrity_spec.spl` | 468 |
| 66 | TODO | general | P3 | Add memory profiling | `test/unit/app/tooling/test_db_performance_spec.spl` | 496 |
| 67 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 246 |
| 68 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 258 |
| 69 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 270 |
| 70 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 282 |
| 71 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/unit/sffi/sffi_public_api_spec.spl` | 131 |
| 72 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/unit/compiler/frontend/parser_spec.spl` | 30 |
| 73 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 74 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_types_spec.spl` | 10 |
| 75 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 76 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_module_spec.spl` | 10 |
| 77 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/unit/compiler/loader/jit_context_spec.spl` | 209 |
| 78 | TODO | general | P3 | Add TypeRegistry validation | `test/unit/compiler/loader/jit_context_spec.spl` | 336 |
| 79 | TODO | general | P3 | Create test template and type args | `test/unit/compiler/loader/jit_context_spec.spl` | 388 |
| 80 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/unit/compiler/loader/jit_context_spec.spl` | 397 |
| 81 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/unit/compiler/loader/jit_context_spec.spl` | 401 |
| 82 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 405 |
| 83 | TODO | general | P3 | Verify DI container passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 409 |
| 84 | TODO | general | P3 | Implement when parser integration complete | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 55 |
| 85 | TODO | general | P3 | Test function compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 62 |
| 86 | TODO | general | P3 | Test class compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 69 |
| 87 | TODO | general | P3 | Test struct compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 76 |
| 88 | TODO | general | P3 | Test enum compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 80 |
| 89 | TODO | general | P3 | Test cross-module method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 96 |
| 90 | TODO | general | P3 | Test generic method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 103 |
| 91 | TODO | general | P3 | Test trait method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 110 |
| 92 | TODO | general | P3 | Test UFCS resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 114 |
| 93 | TODO | general | P3 | Test ambiguity detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 118 |
| 94 | TODO | general | P3 | Test type inference for val bindings | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 134 |
| 95 | TODO | general | P3 | Test return type inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 138 |
| 96 | TODO | general | P3 | Test generic type argument inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 142 |
| 97 | TODO | general | P3 | Test type error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 146 |
| 98 | TODO | general | P3 | Test recursive types | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 150 |
| 99 | TODO | general | P3 | Test parse error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 166 |
| 100 | TODO | general | P3 | Test compilation error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 173 |
| 101 | TODO | general | P3 | Test runtime error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 180 |
| 102 | TODO | general | P3 | Test span/location in errors | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 187 |
| 103 | TODO | general | P3 | Test error suggestions | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 191 |
| 104 | TODO | general | P3 | Test import resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 207 |
| 105 | TODO | general | P3 | Test private symbol hiding | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 214 |
| 106 | TODO | general | P3 | Test circular import detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 218 |
| 107 | TODO | general | P3 | Test dependency graph resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 225 |
| 108 | TODO | general | P3 | Test hot reload | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 229 |
| 109 | TODO | general | P3 | Test scope cleanup | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 245 |
| 110 | TODO | general | P3 | Test cache eviction | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 254 |
| 111 | TODO | general | P3 | Test refcount management | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 258 |
| 112 | TODO | general | P3 | Test leak detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 262 |
| 113 | TODO | general | P3 | Test deep recursion | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 266 |
| 114 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 115 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 116 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 117 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 118 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 119 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 120 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 121 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 122 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 123 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 55 |
| 124 | TODO | general | P3 | Test function compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 62 |
| 125 | TODO | general | P3 | Test class compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 69 |
| 126 | TODO | general | P3 | Test struct compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 76 |
| 127 | TODO | general | P3 | Test enum compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 80 |
| 128 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 96 |
| 129 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 103 |
| 130 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 110 |
| 131 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 114 |
| 132 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 118 |
| 133 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 134 |
| 134 | TODO | general | P3 | Test return type inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 138 |
| 135 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 142 |
| 136 | TODO | general | P3 | Test type error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 146 |
| 137 | TODO | general | P3 | Test recursive types | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 150 |
| 138 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 166 |
| 139 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 173 |
| 140 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 180 |
| 141 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 187 |
| 142 | TODO | general | P3 | Test error suggestions | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 191 |
| 143 | TODO | general | P3 | Test import resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 207 |
| 144 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 214 |
| 145 | TODO | general | P3 | Test circular import detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 218 |
| 146 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 225 |
| 147 | TODO | general | P3 | Test hot reload | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 229 |
| 148 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 245 |
| 149 | TODO | general | P3 | Test cache eviction | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 254 |
| 150 | TODO | general | P3 | Test refcount management | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 258 |
| 151 | TODO | general | P3 | Test leak detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 262 |
| 152 | TODO | general | P3 | Test deep recursion | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 266 |
| 153 | TODO | general | P3 | Create minimal MirModule and compile | `test/integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 154 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 155 | TODO | general | P3 | Implement actual ELF reading | `test/integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 156 | TODO | general | P3 | Implement actual symbol parsing | `test/integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 157 | TODO | general | P3 | Implement actual size measurement | `test/integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 158 | TODO | general | P3 | Verify function order in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 159 | TODO | general | P3 | Verify actual ordering in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 160 | TODO | general | P3 | Verify relocations are correct | `test/integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 161 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 162 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/03_system/generated/spec_matchers_spec.spl` | 115 |
| 163 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 83 |
| 164 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 129 |
| 165 | TODO | sspec-live-capture | P2 | ML live-capture (T2g) blocked: libtorch unavailable, rt_torch_available() returns false. When it returns true, write live_ml_capture_spec.spl per live_audio_capture_spec.spl | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 33 |
| 166 | TODO | sspec-verification | P1 | T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 48 |
| 167 | TODO | llm-caret-messaging | P1 | Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance | `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl` | 110 |
| 168 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1052 |
| 169 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1057 |
| 170 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1062 |
| 171 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1067 |
| 172 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 173 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 89 |
| 174 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 103 |
| 175 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 110 |
| 176 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 66 |
| 177 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 70 |
| 178 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 81 |
| 179 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 85 |
| 180 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 83 |
| 181 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 87 |
| 182 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 91 |
| 183 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/03_system/feature/usage/set_literal_spec.spl` | 36 |
| 184 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/03_system/feature/usage/set_literal_spec.spl` | 77 |
| 185 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 86 |
| 186 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 95 |
| 187 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 120 |
| 188 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 137 |
| 189 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/03_system/feature/usage/trait_coherence_spec.spl` | 381 |
| 190 | TODO | general | P3 | Lambda default parameters not yet supported | `test/03_system/feature/usage/parser_default_keyword_spec.spl` | 189 |
| 191 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/compiler/parser_improvements_spec.spl` | 219 |
| 192 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/system/generated/spec_matchers_spec.spl` | 63 |
| 193 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 83 |
| 194 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 129 |
| 195 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 63 |
| 196 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 67 |
| 197 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 78 |
| 198 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 199 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 64 |
| 200 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 68 |
| 201 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 72 |
| 202 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/compiler/parser_improvements_spec.spl` | 209 |
| 203 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/native_layout_performance_spec.spl` | 52 |
| 204 | TODO | general | P3 | Parse output from time -v or perf stat | `test/05_perf/native_layout_performance_spec.spl` | 66 |
| 205 | TODO | general | P3 | Compile source | `test/05_perf/native_layout_performance_spec.spl` | 75 |
| 206 | TODO | general | P3 | Use file stats | `test/05_perf/native_layout_performance_spec.spl` | 94 |
| 207 | TODO | general | P3 | Compile both versions | `test/05_perf/native_layout_performance_spec.spl` | 152 |
| 208 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 185 |
| 209 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 216 |
| 210 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 250 |
| 211 | TODO | general | P3 | Compile both and compare | `test/05_perf/native_layout_performance_spec.spl` | 286 |
| 212 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/native_layout_performance_spec.spl` | 366 |
| 213 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/native_layout_performance_spec.spl` | 395 |
| 214 | TODO | general | P3 | bench_run_warm + bench_emit require cross-module struct construction | `test/05_perf/web/web_server_bench_spec.spl` | 206 |
| 215 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/05_perf/intensive/http/h3_settings_write_frame_spec.spl` | 17 |
| 216 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/feature/usage/macro_validation_spec.spl` | 206 |
| 217 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/feature/usage/set_literal_spec.spl` | 57 |
| 218 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/feature/usage/set_literal_spec.spl` | 98 |
| 219 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 107 |
| 220 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 116 |
| 221 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 141 |
| 222 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 158 |
| 223 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/feature/usage/trait_coherence_spec.spl` | 365 |
| 224 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/feature/usage/primitive_types_spec.spl` | 84 |
| 225 | TODO | general | P3 | Lambda default parameters not yet supported | `test/feature/usage/parser_default_keyword_spec.spl` | 172 |
| 226 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 54 |
| 227 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 61 |
| 228 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 70 |
| 229 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 77 |
| 230 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 86 |
| 231 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 93 |
| 232 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 121 |
| 233 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 130 |
| 234 | TODO | general | P3 | Simulate write failure | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 137 |
| 235 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 146 |
| 236 | TODO | general | P3 | Implement after process spawning is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 155 |
| 237 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/01_unit/app/tooling/test_db_integrity_spec.spl` | 470 |
| 238 | TODO | general | P3 | Add memory profiling | `test/01_unit/app/tooling/test_db_performance_spec.spl` | 484 |
| 239 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/parser_spec.spl` | 209 |
| 240 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 241 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_types_spec.spl` | 10 |
| 242 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 243 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_module_spec.spl` | 10 |
| 244 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/01_unit/compiler/loader/jit_context_spec.spl` | 209 |
| 245 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 336 |
| 246 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/jit_context_spec.spl` | 388 |
| 247 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/jit_context_spec.spl` | 397 |
| 248 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/jit_context_spec.spl` | 401 |
| 249 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 405 |
| 250 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 409 |
| 251 | TODO | general | P3 | Execute binary and wait for completion | `test/perf/native_layout_performance_spec.spl` | 46 |
| 252 | TODO | general | P3 | Parse output from time -v or perf stat | `test/perf/native_layout_performance_spec.spl` | 60 |
| 253 | TODO | general | P3 | Compile source | `test/perf/native_layout_performance_spec.spl` | 69 |
| 254 | TODO | general | P3 | Use file stats | `test/perf/native_layout_performance_spec.spl` | 88 |
| 255 | TODO | general | P3 | Compile both versions | `test/perf/native_layout_performance_spec.spl` | 141 |
| 256 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 172 |
| 257 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 201 |
| 258 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 233 |
| 259 | TODO | general | P3 | Compile both and compare | `test/perf/native_layout_performance_spec.spl` | 267 |
| 260 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/perf/native_layout_performance_spec.spl` | 341 |
| 261 | TODO | general | P3 | Benchmark actual execution | `test/perf/native_layout_performance_spec.spl` | 368 |
| 262 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/perf/intensive/http/h3_settings_write_frame_spec.spl` | 13 |
| 263 | TODO | rendering | P0 | BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command. | `doc/03_plan/sys_test/render_lane_mission_showcase.md` | 53 |
| 264 | TODO | gpu | P2 | Exercise the DirectX provider probe on a Windows or DXVK host | `doc/08_tracking/todo/gpu_directx_provider_probe_never_exercised_2026-09-06.md` | 1 |
| 265 | TODO | general | P3 | SOSIX runtime unification — blocked rows (resume conditions) | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 1 |
| 266 | TODO | general | P3 | (sosix F1) land the GPU G1 proxy storage slice on a host with a real GPU and a deployed pure-Simple binary; resume via doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md lanes B/C | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 44 |
| 267 | TODO | general | P3 | (sosix AC-3b) prove the QEMU serial row with observed bytes once a pure-Simple compiler accepted by simple_binary_is_valid is deployed; publish via produce-sosix-qemu-native-pass-bundle.shs and import via collect-sosix-qemu-evidence.shs | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 46 |
| 268 | TODO | general | P3 | (sosix G4) implement the SimpleOS device-initiated queues GQ-001..012 after the GQ-001 native capability report on real hardware | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 48 |
| 269 | TODO | general | P3 | (sosix startup-ab) re-run check-startup-size-performance-audit.shs on a host where its Simple probe rows do not exit 127, and diff against doc/09_report/startup_size_performance_audit_2026-05-27.md | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 50 |
| 270 | TODO | general | P3 | (sosix A5) drop the one-line `export use` shims for aliased re-exports once the compiler accepts `export use ... as`; until then every shim in src/os/sosix/core re-exports without renaming | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 52 |
| 271 | TODO | test | P2 | Build (or restore) the Jupyter full-server and notebook-exec E2E helpers | `doc/08_tracking/todo/jupyter_e2e_helper_scripts_missing_2026-08-08.md` | 15 |
| 272 | TODO | gpu | P2 | Promote a provider from routing_only to full once fences and phases exist | `doc/08_tracking/todo/gpu_no_provider_reaches_full_conformance_2026-09-06.md` | 1 |
| 273 | TODO | infra | P3 | Build the native HTTPServer benchmark gate scripts or drop the claim | `doc/08_tracking/todo/native_httpserver_benchmark_gate_scripts_missing_2026-08-08.md` | 18 |
| 274 | TODO | general | P3 | bind protected DBFS objects to production descriptor owners | `doc/08_tracking/todo/server_data_namespace_fd_binding_v1.md` | 1 |
| 275 | TODO | test | P1 | Re-run every GPU scheduler spec on a redeployed full-CLI pure-Simple binary | `doc/08_tracking/todo/gpu_scheduler_specs_need_selfhosted_rerun_2026-09-06.md` | 1 |
| 276 | TODO | general | P3 | hardening plan — resume after the bootstrap seed redeploy is stable | `doc/08_tracking/todo/hardening_resume_after_seed_redeploy_2026-08-25.md` | 1 |
| 277 | TODO | general | P3 | Route dynamic manifest passes to a real execution path | `doc/08_tracking/todo/optimizer_manifest_dynamic_pass_routing_2026-08-18.md` | 1 |
| 278 | TODO | gpu | P2 | Make the resident-slice readback counter a real measurement or delete it | `doc/08_tracking/todo/gpu_resident_readback_counter_unmeasurable_2026-09-06.md` | 1 |
| 279 | TODO | gpu | P2 | Exercise the Metal provider probe on a host where metal_available() is true | `doc/08_tracking/todo/gpu_metal_provider_probe_never_exercised_2026-09-06.md` | 1 |
| 280 | TODO | general | P3 | the workspace root guard cannot fail in CI (vacuous gate) | `doc/08_tracking/todo/workspace_root_guard_is_vacuous_in_ci_2026-07-28.md` | 1 |
| 281 | TODO | gpu | P2 | Qualify Vulkan resident-2D device evidence with real timestamps and uploaded rows | `doc/08_tracking/todo/gpu_resident_vulkan_device_evidence_unqualified_2026-09-06.md` | 1 |
| 282 | TODO | spipe_docgen | P2 | Render per-cell `%%mode` lane badges in notebook spec manuals | `doc/08_tracking/todo/spipe_docgen_lane_badges_2026-08-08.md` | 5 |
| 283 | TODO | general | P3 | test_runner_execute -> composite -> gpu_lane eager imports cost ~40s of seed-interpreter load | `doc/08_tracking/todo/test_runner_execute_composite_gpu_eager_import_cost_2026-08-17.md` | 1 |
| 284 | TODO | general | P3 | std.async.runtime cannot wake clock-based (timer/sleep) futures | `doc/08_tracking/todo/async_runtime_timer_wakeup_for_sleep_2026-08-17.md` | 1 |
| 285 | TODO | sspec-maintain | P1 | Enhance scoring rules to recognize lane-gated notebook specs | `doc/08_tracking/todo/sspec_maintain_lane_aware_scoring_2026-08-08.md` | 5 |
| 286 | TODO | general | P3 | admit SFFI providers with artifact-bound evidence | `doc/08_tracking/todo/sffi_v2_provider_admission_2026-08-27.md` | 1 |
| 287 | TODO | bootstrap | P2 | Build `scripts/bootstrap/rollback-bootstrap-deploy.shs` | `doc/08_tracking/todo/rollback_bootstrap_deploy_script_missing_2026-08-08.md` | 11 |
| 288 | TODO | uno_q | P2 | POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 16 |
| 289 | TODO | cosmos | P0 | POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 17 |
