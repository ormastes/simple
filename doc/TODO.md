# TODO Tracking

**Total:** 268 items | **Open:** 265 | **Blocked:** 3

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 1 |
| P1 | 3 |
| P2 | 7 |
| P3 | 257 |

## By Area

| Area | Count |
|------|-------|
| bootstrap | 1 |
| cosmos | 1 |
| general | 256 |
| infra | 1 |
| llm-caret-messaging | 1 |
| spipe_docgen | 1 |
| sspec-live-capture | 1 |
| sspec-maintain | 1 |
| sspec-verification | 1 |
| test | 1 |
| ui | 2 |
| uno_q | 1 |

## P0 Critical

- [TODO] **POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured.** - `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md:17`

## P1 High Priority

- [TODO] T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it - `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl:47`
- [TODO] Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance - `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:110`
- [TODO] Enhance scoring rules to recognize lane-gated notebook specs - `doc/08_tracking/todo/sspec_maintain_lane_aware_scoring_2026-08-08.md:5`

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/system_api.spl` | 130 |
| 1 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 2 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 3 | TODO | general | P3 | lower to csrs in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 4 | TODO | general | P3 | lower to csrc in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 5 | TODO | general | P3 | lower to csrrw in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 6 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/semihost_transport.spl` | 302 |
| 7 | TODO | general | P3 | (gpu) expose cudaMemcpyPeer / cuMemcpyPeer so multi-GPU transfers do not have | `src/lib/nogc_sync_mut/io/cuda_sffi.spl` | 126 |
| 8 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 9 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 10 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 11 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 12 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 13 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 14 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 15 | TODO | ui | P2 | vbox does not honour the `flex` prop at all — it counts children | `src/lib/common/ui/layout.spl` | 123 |
| 16 | TODO | ui | P2 | these accessors return LOGICAL units, but layout_vbox/layout_hbox | `src/lib/common/ui/layout.spl` | 429 |
| 17 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 18 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 19 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `src/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 20 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 21 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 22 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 23 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 24 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 25 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 26 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `src/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 27 | TODO | general | P3 | (gpu) model shared-memory exchange and a real gpu_syncthreads barrier in this | `src/lib/gc_async_mut/gpu_ops.spl` | 462 |
| 28 | TODO | general | P3 | wire up hwprobe when available | `src/compiler/30.types/simd_capabilities.spl` | 349 |
| 29 | TODO | general | P3 | promote this to self.error_fatal (with an Unreachable MIR | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 2773 |
| 30 | TODO | general | P3 | this arm is an incomplete port. The Rust original | `src/compiler/35.semantics/macro_contracts.spl` | 111 |
| 31 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `src/compiler/80.driver/watcher/watcher_daemon.spl` | 76 |
| 32 | TODO | general | P3 | `has_current_lines` is an unresolved name (porter artifact); it is | `src/compiler/90.tools/text_diff.spl` | 102 |
| 33 | TODO | general | P3 | `_srv_u8_at` currently has no in-file call site even though the old | `src/os/tls13/server.spl` | 67 |
| 34 | TODO | general | P3 | when netstack is wired, call net_service_poll() here to drive | `src/os/kernel/net/driver_shim.spl` | 337 |
| 35 | TODO | general | P3 | Implement ValueBuilder and complete handler integration | `src/compiler_rust/lib/std/src/sdn/handler.spl` | 205 |
| 36 | TODO | general | P3 | url_encode should percent-encode each UTF-8 BYTE (%C3%A9), not | `src/compiler_rust/lib/std/src/tooling/url_utils.spl` | 125 |
| 37 | TODO | general | P3 | add more about copy-paste and human readability. | `src/compiler_rust/vendor/shlex/src/quoting_warning.md` | 365 |
| 38 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `src/app/devhub/cmd_daily_debug.spl` | 165 |
| 39 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/perf/intensive/http/h3_settings_write_frame_spec.spl` | 20 |
| 40 | TODO | general | P3 | Execute binary and wait for completion | `test/perf/native_layout_performance_spec.spl` | 53 |
| 41 | TODO | general | P3 | Parse output from time -v or perf stat | `test/perf/native_layout_performance_spec.spl` | 68 |
| 42 | TODO | general | P3 | Compile source | `test/perf/native_layout_performance_spec.spl` | 78 |
| 43 | TODO | general | P3 | Use file stats | `test/perf/native_layout_performance_spec.spl` | 97 |
| 44 | TODO | general | P3 | Compile both versions | `test/perf/native_layout_performance_spec.spl` | 156 |
| 45 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 194 |
| 46 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 228 |
| 47 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 266 |
| 48 | TODO | general | P3 | Compile both and compare | `test/perf/native_layout_performance_spec.spl` | 302 |
| 49 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/perf/native_layout_performance_spec.spl` | 384 |
| 50 | TODO | general | P3 | Benchmark actual execution | `test/perf/native_layout_performance_spec.spl` | 423 |
| 51 | TODO | general | P3 | Lambda default parameters not yet supported | `test/feature/usage/parser_default_keyword_spec.spl` | 189 |
| 52 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/feature/usage/trait_coherence_spec.spl` | 381 |
| 53 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/feature/usage/macro_validation_spec.spl` | 210 |
| 54 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/feature/usage/primitive_types_spec.spl` | 72 |
| 55 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/feature/usage/set_literal_spec.spl` | 40 |
| 56 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/feature/usage/set_literal_spec.spl` | 95 |
| 57 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 106 |
| 58 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 117 |
| 59 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 148 |
| 60 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 167 |
| 61 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/parser_spec.spl` | 248 |
| 62 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/01_unit/compiler/loader/jit_context_spec.spl` | 225 |
| 63 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 362 |
| 64 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/jit_context_spec.spl` | 419 |
| 65 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/jit_context_spec.spl` | 429 |
| 66 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/jit_context_spec.spl` | 434 |
| 67 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 439 |
| 68 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 444 |
| 69 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_lower_spec.spl` | 16 |
| 70 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_types_spec.spl` | 14 |
| 71 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_eval_spec.spl` | 16 |
| 72 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_module_spec.spl` | 16 |
| 73 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 53 |
| 74 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 60 |
| 75 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 69 |
| 76 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 76 |
| 77 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 85 |
| 78 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 92 |
| 79 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 120 |
| 80 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 129 |
| 81 | TODO | general | P3 | Simulate write failure | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 136 |
| 82 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 145 |
| 83 | TODO | general | P3 | Implement after process spawning is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 154 |
| 84 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/01_unit/app/tooling/test_db_integrity_spec.spl` | 470 |
| 85 | TODO | general | P3 | Add memory profiling | `test/01_unit/app/tooling/test_db_performance_spec.spl` | 498 |
| 86 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/db/.spipe_wrapped_entry_db_ram_vs_persistent_bench_spec.spl` | 430 |
| 87 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` | 371 |
| 88 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/05_perf/intensive/http/h3_settings_write_frame_spec.spl` | 17 |
| 89 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/native_layout_performance_spec.spl` | 52 |
| 90 | TODO | general | P3 | Parse output from time -v or perf stat | `test/05_perf/native_layout_performance_spec.spl` | 66 |
| 91 | TODO | general | P3 | Compile source | `test/05_perf/native_layout_performance_spec.spl` | 75 |
| 92 | TODO | general | P3 | Use file stats | `test/05_perf/native_layout_performance_spec.spl` | 94 |
| 93 | TODO | general | P3 | Compile both versions | `test/05_perf/native_layout_performance_spec.spl` | 152 |
| 94 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 185 |
| 95 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 216 |
| 96 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 250 |
| 97 | TODO | general | P3 | Compile both and compare | `test/05_perf/native_layout_performance_spec.spl` | 286 |
| 98 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/native_layout_performance_spec.spl` | 366 |
| 99 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/native_layout_performance_spec.spl` | 395 |
| 100 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 77 |
| 101 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 83 |
| 102 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 96 |
| 103 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 102 |
| 104 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 73 |
| 105 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 79 |
| 106 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 85 |
| 107 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 73 |
| 108 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 80 |
| 109 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 94 |
| 110 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 101 |
| 111 | TODO | general | P3 | Lambda default parameters not yet supported | `test/03_system/feature/usage/parser_default_keyword_spec.spl` | 189 |
| 112 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/03_system/feature/usage/trait_coherence_spec.spl` | 381 |
| 113 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/03_system/feature/usage/macro_validation_spec.spl` | 210 |
| 114 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/03_system/feature/usage/primitive_types_spec.spl` | 72 |
| 115 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/03_system/feature/usage/set_literal_spec.spl` | 40 |
| 116 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/03_system/feature/usage/set_literal_spec.spl` | 95 |
| 117 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 106 |
| 118 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 117 |
| 119 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 148 |
| 120 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 167 |
| 121 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1130 |
| 122 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1135 |
| 123 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1140 |
| 124 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1145 |
| 125 | TODO | sspec-live-capture | P2 | ML live-capture (T2g) blocked: libtorch unavailable, rt_torch_available() returns false. When it returns true, write live_ml_capture_spec.spl per live_audio_capture_spec.spl | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 32 |
| 126 | TODO | sspec-verification | P1 | T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 47 |
| 127 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 83 |
| 128 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 129 |
| 129 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/compiler/parser_improvements_spec.spl` | 219 |
| 130 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/03_system/generated/spec_matchers_spec.spl` | 92 |
| 131 | TODO | llm-caret-messaging | P1 | Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance | `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl` | 110 |
| 132 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 133 | TODO | general | P3 | Implement actual ELF reading | `test/integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 134 | TODO | general | P3 | Implement actual symbol parsing | `test/integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 135 | TODO | general | P3 | Implement actual size measurement | `test/integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 136 | TODO | general | P3 | Verify function order in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 137 | TODO | general | P3 | Verify actual ordering in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 138 | TODO | general | P3 | Verify relocations are correct | `test/integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 139 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 140 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 70 |
| 141 | TODO | general | P3 | Test function compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 80 |
| 142 | TODO | general | P3 | Test class compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 90 |
| 143 | TODO | general | P3 | Test struct compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 100 |
| 144 | TODO | general | P3 | Test enum compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 107 |
| 145 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 126 |
| 146 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 136 |
| 147 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 146 |
| 148 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 153 |
| 149 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 160 |
| 150 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 179 |
| 151 | TODO | general | P3 | Test return type inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 186 |
| 152 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 193 |
| 153 | TODO | general | P3 | Test type error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 200 |
| 154 | TODO | general | P3 | Test recursive types | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 207 |
| 155 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 226 |
| 156 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 236 |
| 157 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 246 |
| 158 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 256 |
| 159 | TODO | general | P3 | Test error suggestions | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 263 |
| 160 | TODO | general | P3 | Test import resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 282 |
| 161 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 292 |
| 162 | TODO | general | P3 | Test circular import detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 299 |
| 163 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 309 |
| 164 | TODO | general | P3 | Test hot reload | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 316 |
| 165 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 335 |
| 166 | TODO | general | P3 | Test cache eviction | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 347 |
| 167 | TODO | general | P3 | Test refcount management | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 354 |
| 168 | TODO | general | P3 | Test leak detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 361 |
| 169 | TODO | general | P3 | Test deep recursion | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 368 |
| 170 | TODO | general | P3 | Create minimal MirModule and compile | `test/integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 171 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/unit/sffi/sffi_public_api_spec.spl` | 131 |
| 172 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/unit/compiler/frontend/parser_spec.spl` | 45 |
| 173 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/unit/compiler/loader/jit_context_spec.spl` | 225 |
| 174 | TODO | general | P3 | Add TypeRegistry validation | `test/unit/compiler/loader/jit_context_spec.spl` | 362 |
| 175 | TODO | general | P3 | Create test template and type args | `test/unit/compiler/loader/jit_context_spec.spl` | 419 |
| 176 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/unit/compiler/loader/jit_context_spec.spl` | 429 |
| 177 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/unit/compiler/loader/jit_context_spec.spl` | 434 |
| 178 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 439 |
| 179 | TODO | general | P3 | Verify DI container passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 444 |
| 180 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_lower_spec.spl` | 14 |
| 181 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_types_spec.spl` | 14 |
| 182 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_eval_spec.spl` | 14 |
| 183 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_module_spec.spl` | 14 |
| 184 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 299 |
| 185 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 313 |
| 186 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 327 |
| 187 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 341 |
| 188 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 51 |
| 189 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 58 |
| 190 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 67 |
| 191 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 74 |
| 192 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 83 |
| 193 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 90 |
| 194 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 118 |
| 195 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 127 |
| 196 | TODO | general | P3 | Simulate write failure | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 134 |
| 197 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 143 |
| 198 | TODO | general | P3 | Implement after process spawning is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 152 |
| 199 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/unit/app/tooling/test_db_integrity_spec.spl` | 468 |
| 200 | TODO | general | P3 | Add memory profiling | `test/unit/app/tooling/test_db_performance_spec.spl` | 496 |
| 201 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 18 |
| 202 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 24 |
| 203 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 30 |
| 204 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 36 |
| 205 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 131 |
| 206 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 164 |
| 207 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 293 |
| 208 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 375 |
| 209 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 210 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 211 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 212 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 213 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 214 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 215 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 216 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 217 | TODO | general | P3 | Implement when parser integration complete | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 70 |
| 218 | TODO | general | P3 | Test function compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 80 |
| 219 | TODO | general | P3 | Test class compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 90 |
| 220 | TODO | general | P3 | Test struct compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 100 |
| 221 | TODO | general | P3 | Test enum compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 107 |
| 222 | TODO | general | P3 | Test cross-module method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 126 |
| 223 | TODO | general | P3 | Test generic method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 136 |
| 224 | TODO | general | P3 | Test trait method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 146 |
| 225 | TODO | general | P3 | Test UFCS resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 153 |
| 226 | TODO | general | P3 | Test ambiguity detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 160 |
| 227 | TODO | general | P3 | Test type inference for val bindings | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 179 |
| 228 | TODO | general | P3 | Test return type inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 186 |
| 229 | TODO | general | P3 | Test generic type argument inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 193 |
| 230 | TODO | general | P3 | Test type error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 200 |
| 231 | TODO | general | P3 | Test recursive types | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 207 |
| 232 | TODO | general | P3 | Test parse error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 226 |
| 233 | TODO | general | P3 | Test compilation error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 236 |
| 234 | TODO | general | P3 | Test runtime error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 246 |
| 235 | TODO | general | P3 | Test span/location in errors | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 256 |
| 236 | TODO | general | P3 | Test error suggestions | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 263 |
| 237 | TODO | general | P3 | Test import resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 282 |
| 238 | TODO | general | P3 | Test private symbol hiding | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 292 |
| 239 | TODO | general | P3 | Test circular import detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 299 |
| 240 | TODO | general | P3 | Test dependency graph resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 309 |
| 241 | TODO | general | P3 | Test hot reload | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 316 |
| 242 | TODO | general | P3 | Test scope cleanup | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 335 |
| 243 | TODO | general | P3 | Test cache eviction | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 347 |
| 244 | TODO | general | P3 | Test refcount management | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 354 |
| 245 | TODO | general | P3 | Test leak detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 361 |
| 246 | TODO | general | P3 | Test deep recursion | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 368 |
| 247 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 248 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 72 |
| 249 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 78 |
| 250 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 91 |
| 251 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 97 |
| 252 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 83 |
| 253 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 129 |
| 254 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/compiler/parser_improvements_spec.spl` | 209 |
| 255 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/system/generated/spec_matchers_spec.spl` | 92 |
| 256 | TODO | general | P3 | the workspace root guard cannot fail in CI (vacuous gate) | `doc/08_tracking/todo/workspace_root_guard_is_vacuous_in_ci_2026-07-28.md` | 1 |
| 257 | TODO | uno_q | P2 | POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 16 |
| 258 | TODO | cosmos | P0 | POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 17 |
| 259 | TODO | general | P3 | test_runner_execute -> composite -> gpu_lane eager imports cost ~40s of seed-interpreter load | `doc/08_tracking/todo/test_runner_execute_composite_gpu_eager_import_cost_2026-08-17.md` | 1 |
| 260 | TODO | infra | P3 | Build the native HTTPServer benchmark gate scripts or drop the claim | `doc/08_tracking/todo/native_httpserver_benchmark_gate_scripts_missing_2026-08-08.md` | 18 |
| 261 | TODO | general | P3 | hardening plan — resume after the bootstrap seed redeploy is stable | `doc/08_tracking/todo/hardening_resume_after_seed_redeploy_2026-08-25.md` | 1 |
| 262 | TODO | general | P3 | std.async.runtime cannot wake clock-based (timer/sleep) futures | `doc/08_tracking/todo/async_runtime_timer_wakeup_for_sleep_2026-08-17.md` | 1 |
| 263 | TODO | bootstrap | P2 | Build `scripts/bootstrap/rollback-bootstrap-deploy.shs` | `doc/08_tracking/todo/rollback_bootstrap_deploy_script_missing_2026-08-08.md` | 11 |
| 264 | TODO | spipe_docgen | P2 | Render per-cell `%%mode` lane badges in notebook spec manuals | `doc/08_tracking/todo/spipe_docgen_lane_badges_2026-08-08.md` | 5 |
| 265 | TODO | general | P3 | Route dynamic manifest passes to a real execution path | `doc/08_tracking/todo/optimizer_manifest_dynamic_pass_routing_2026-08-18.md` | 1 |
| 266 | TODO | sspec-maintain | P1 | Enhance scoring rules to recognize lane-gated notebook specs | `doc/08_tracking/todo/sspec_maintain_lane_aware_scoring_2026-08-08.md` | 5 |
| 267 | TODO | test | P2 | Build (or restore) the Jupyter full-server and notebook-exec E2E helpers | `doc/08_tracking/todo/jupyter_e2e_helper_scripts_missing_2026-08-08.md` | 15 |
