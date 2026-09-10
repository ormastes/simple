# TODO Tracking

**Total:** 285 items | **Open:** 279 | **Blocked:** 6

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 2 |
| P1 | 7 |
| P2 | 10 |
| P3 | 266 |

## By Area

| Area | Count |
|------|-------|
| sspec-verification | 1 |
| compiler | 1 |
| llm-caret-messaging | 1 |
| llm-caret | 3 |
| test | 1 |
| general | 265 |
| sspec-live-capture | 1 |
| uno_q | 1 |
| rendering | 1 |
| compiler-resolver | 2 |
| llm-caret-server | 1 |
| cosmos | 1 |
| sspec-maintain | 1 |
| bootstrap | 1 |
| ui | 2 |
| spipe_docgen | 1 |
| infra | 1 |

## P0 Critical

- [TODO] **POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured.** - `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md:17`
- [TODO] **BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command.** - `doc/03_plan/sys_test/render_lane_mission_showcase.md:53`

## P1 High Priority

- [TODO] Resolve STUB-002: either implement effect inference - `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:954`
- [TODO] Remove this rename workaround once the seed resolves bare names by import scope instead of a global registry: a function's own parameter must win over a same-named imported module (doc/08_tracking/bug/module_name_shadows_function_parameter_2026-09-06.md) - `src/lib/nogc_sync_mut/http_server/server.spl:219`
- [TODO] SffiHttpMethod/SffiHttpResponse/SffiHttpStatus are named apart from http_server's HttpMethod/HttpResponse/HttpStatus only because the seed resolves type and enum-variant names globally by bare name; restore the plain names once resolution is import-scoped (doc/08_tracking/bug/enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06.md) - `src/lib/nogc_sync_mut/io/http_sffi.spl:122`
- [TODO] Reports every live agent as exited on the shipped binary: the seed's rt_process_is_running returns false for any pid it did not spawn and a tmux pane is tmux's child; fixed in source, needs the deploy (doc/08_tracking/bug/interpreter_process_is_running_false_for_unspawned_pid_2026-09-06.md) - `src/app/llm_caret/cs_dashboard.spl:269`
- [TODO] T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it - `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl:48`
- [TODO] Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance - `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl:110`
- [TODO] Enhance scoring rules to recognize lane-gated notebook specs - `doc/08_tracking/todo/sspec_maintain_lane_aware_scoring_2026-08-08.md:5`

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | `has_current_lines` is an unresolved name (porter artifact); it is | `src/compiler/90.tools/text_diff.spl` | 102 |
| 1 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `src/compiler/80.driver/watcher/watcher_daemon.spl` | 73 |
| 2 | TODO | compiler | P1 | Resolve STUB-002: either implement effect inference | `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` | 954 |
| 3 | TODO | general | P3 | wire up hwprobe when available | `src/compiler/30.types/simd_capabilities.spl` | 416 |
| 4 | TODO | general | P3 | this arm is an incomplete port. The Rust original | `src/compiler/35.semantics/macro_contracts.spl` | 111 |
| 5 | TODO | general | P3 | promote this to self.error_fatal (with an Unreachable MIR | `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 2873 |
| 6 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/system_api.spl` | 130 |
| 7 | TODO | general | P3 | restore the per-architecture trap once `@cfg("target_arch", ...)` gates | `src/lib/nogc_async_mut_noalloc/baremetal/semihost_transport.spl` | 307 |
| 8 | TODO | general | P3 | (gpu) model shared-memory exchange and a real gpu_syncthreads barrier in this | `src/lib/gc_async_mut/gpu_ops.spl` | 462 |
| 9 | TODO | compiler-resolver | P1 | Remove this rename workaround once the seed resolves bare names by import scope instead of a global registry: a function's own parameter must win over a same-named imported module (doc/08_tracking/bug/module_name_shadows_function_parameter_2026-09-06.md) | `src/lib/nogc_sync_mut/http_server/server.spl` | 219 |
| 10 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 11 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 12 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 13 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 14 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 15 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 16 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 17 | TODO | compiler-resolver | P1 | SffiHttpMethod/SffiHttpResponse/SffiHttpStatus are named apart from http_server's HttpMethod/HttpResponse/HttpStatus only because the seed resolves type and enum-variant names globally by bare name; restore the plain names once resolution is import-scoped (doc/08_tracking/bug/enum_variant_resolved_globally_by_bare_name_httpmethod_collision_2026-09-06.md) | `src/lib/nogc_sync_mut/io/http_sffi.spl` | 122 |
| 18 | TODO | general | P3 | (gpu) expose cudaMemcpyPeer / cuMemcpyPeer so multi-GPU transfers do not have | `src/lib/nogc_sync_mut/io/cuda_sffi.spl` | 151 |
| 19 | TODO | ui | P2 | vbox does not honour the `flex` prop at all — it counts children | `src/lib/common/ui/layout.spl` | 123 |
| 20 | TODO | ui | P2 | these accessors return LOGICAL units, but layout_vbox/layout_hbox | `src/lib/common/ui/layout.spl` | 429 |
| 21 | TODO | general | P3 | (sosix C3) prove the zero-wrapper lowering once native-build works on this | `src/lib/nogc_async_mut/sosix/posix.spl` | 19 |
| 22 | TODO | general | P3 | (sosix C4) replace this reference provider with a Linux io_uring provider | `src/lib/nogc_async_mut/sosix/file_driver.spl` | 13 |
| 23 | TODO | general | P3 | (sosix C5) add the macOS and Windows providers on a host that has them; this | `src/lib/nogc_async_mut/sosix/file_driver.spl` | 16 |
| 24 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `src/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 25 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 26 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 27 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 28 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 29 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 30 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 31 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 32 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 33 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `src/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 34 | TODO | general | P3 | url_encode should percent-encode each UTF-8 BYTE (%C3%A9), not | `src/compiler_rust/lib/std/src/tooling/url_utils.spl` | 125 |
| 35 | TODO | general | P3 | Implement ValueBuilder and complete handler integration | `src/compiler_rust/lib/std/src/sdn/handler.spl` | 205 |
| 36 | TODO | general | P3 | add more about copy-paste and human readability. | `src/compiler_rust/vendor/shlex/src/quoting_warning.md` | 365 |
| 37 | TODO | general | P3 | (sosix G3) retire this route onto the v1 positioned stack once the QEMU | `src/os/sosix/io_rw.spl` | 14 |
| 38 | TODO | general | P3 | when netstack is wired, call net_service_poll() here to drive | `src/os/kernel/net/driver_shim.spl` | 337 |
| 39 | TODO | llm-caret-server | P2 | The whole SSE body is built and returned at once; real SDK streaming wants chunked token-by-token delivery. Frame shapes are already correct, so this is a transport change, not a format one | `src/app/llm_caret/server.spl` | 212 |
| 40 | TODO | llm-caret | P1 | Reports every live agent as exited on the shipped binary: the seed's rt_process_is_running returns false for any pid it did not spawn and a tmux pane is tmux's child; fixed in source, needs the deploy (doc/08_tracking/bug/interpreter_process_is_running_false_for_unspawned_pid_2026-09-06.md) | `src/app/llm_caret/cs_dashboard.spl` | 269 |
| 41 | TODO | llm-caret | P2 | Delete this EOF ceiling once the fixed seed ships; same workaround as chat_tui.spl and obsolete for the same reason | `src/app/llm_caret/cs_main.spl` | 35 |
| 42 | TODO | llm-caret | P2 | Delete this EOF ceiling and rely on the loop's existing nil branch once the fixed seed ships; removing it earlier breaks caret on the current binary (doc/08_tracking/bug/seed_interpreter_stdin_read_line_erases_eof_2026-09-06.md) | `src/app/llm_caret/chat_tui.spl` | 745 |
| 43 | TODO | general | P3 | Import bugdb handlers when available | `src/app/mcp/bootstrap/main_optimized.spl` | 244 |
| 44 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `src/app/devhub/cmd_daily_debug.spl` | 165 |
| 45 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `src/app/itf/cmd_daily_debug.spl` | 159 |
| 46 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/compiler/parser_improvements_spec.spl` | 219 |
| 47 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/03_system/generated/spec_matchers_spec.spl` | 115 |
| 48 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/03_system/feature/usage/set_literal_spec.spl` | 36 |
| 49 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/03_system/feature/usage/set_literal_spec.spl` | 77 |
| 50 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 86 |
| 51 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 95 |
| 52 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 120 |
| 53 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 137 |
| 54 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/03_system/feature/usage/primitive_types_spec.spl` | 64 |
| 55 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/03_system/feature/usage/macro_validation_spec.spl` | 186 |
| 56 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/03_system/feature/usage/trait_coherence_spec.spl` | 381 |
| 57 | TODO | general | P3 | Lambda default parameters not yet supported | `test/03_system/feature/usage/parser_default_keyword_spec.spl` | 189 |
| 58 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 59 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 89 |
| 60 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 103 |
| 61 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 110 |
| 62 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 83 |
| 63 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 87 |
| 64 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 91 |
| 65 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 66 |
| 66 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 70 |
| 67 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 81 |
| 68 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 85 |
| 69 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1052 |
| 70 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1057 |
| 71 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1062 |
| 72 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1067 |
| 73 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 83 |
| 74 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 129 |
| 75 | TODO | sspec-live-capture | P2 | ML live-capture (T2g) blocked: libtorch unavailable, rt_torch_available() returns false. When it returns true, write live_ml_capture_spec.spl per live_audio_capture_spec.spl | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 33 |
| 76 | TODO | sspec-verification | P1 | T1 gate open: all Modern SSpec evidence verified on the Rust bootstrap seed. When a self-hosted binary is deployed, re-run the evidence specs + docgen gate on it | `test/03_system/tools/spipe/examples/live_capture_blocker_sentinels_spec.spl` | 48 |
| 77 | TODO | llm-caret-messaging | P1 | Run the Phase 4 full-CLI and Caret carrier verification with the exact source-matched candidate after Stage 4 admission; retain binary SHA-256, command outputs, and carrier provenance | `test/03_system/app/llm_caret/feature/llm_caret_messaging_phase_cli_spec.spl` | 110 |
| 78 | TODO | general | P3 | Implement when parser integration complete | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 55 |
| 79 | TODO | general | P3 | Test function compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 62 |
| 80 | TODO | general | P3 | Test class compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 69 |
| 81 | TODO | general | P3 | Test struct compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 76 |
| 82 | TODO | general | P3 | Test enum compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 80 |
| 83 | TODO | general | P3 | Test cross-module method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 96 |
| 84 | TODO | general | P3 | Test generic method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 103 |
| 85 | TODO | general | P3 | Test trait method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 110 |
| 86 | TODO | general | P3 | Test UFCS resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 114 |
| 87 | TODO | general | P3 | Test ambiguity detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 118 |
| 88 | TODO | general | P3 | Test type inference for val bindings | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 134 |
| 89 | TODO | general | P3 | Test return type inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 138 |
| 90 | TODO | general | P3 | Test generic type argument inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 142 |
| 91 | TODO | general | P3 | Test type error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 146 |
| 92 | TODO | general | P3 | Test recursive types | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 150 |
| 93 | TODO | general | P3 | Test parse error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 166 |
| 94 | TODO | general | P3 | Test compilation error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 173 |
| 95 | TODO | general | P3 | Test runtime error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 180 |
| 96 | TODO | general | P3 | Test span/location in errors | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 187 |
| 97 | TODO | general | P3 | Test error suggestions | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 191 |
| 98 | TODO | general | P3 | Test import resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 207 |
| 99 | TODO | general | P3 | Test private symbol hiding | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 214 |
| 100 | TODO | general | P3 | Test circular import detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 218 |
| 101 | TODO | general | P3 | Test dependency graph resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 225 |
| 102 | TODO | general | P3 | Test hot reload | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 229 |
| 103 | TODO | general | P3 | Test scope cleanup | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 245 |
| 104 | TODO | general | P3 | Test cache eviction | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 254 |
| 105 | TODO | general | P3 | Test refcount management | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 258 |
| 106 | TODO | general | P3 | Test leak detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 262 |
| 107 | TODO | general | P3 | Test deep recursion | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 266 |
| 108 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 109 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 110 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 111 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 112 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 113 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 114 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 115 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 116 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 117 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/feature/usage/set_literal_spec.spl` | 57 |
| 118 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/feature/usage/set_literal_spec.spl` | 98 |
| 119 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 107 |
| 120 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 116 |
| 121 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 141 |
| 122 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 158 |
| 123 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/feature/usage/primitive_types_spec.spl` | 84 |
| 124 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/feature/usage/macro_validation_spec.spl` | 206 |
| 125 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/feature/usage/trait_coherence_spec.spl` | 365 |
| 126 | TODO | general | P3 | Lambda default parameters not yet supported | `test/feature/usage/parser_default_keyword_spec.spl` | 172 |
| 127 | TODO | general | P3 | Execute binary and wait for completion | `test/perf/native_layout_performance_spec.spl` | 46 |
| 128 | TODO | general | P3 | Parse output from time -v or perf stat | `test/perf/native_layout_performance_spec.spl` | 60 |
| 129 | TODO | general | P3 | Compile source | `test/perf/native_layout_performance_spec.spl` | 69 |
| 130 | TODO | general | P3 | Use file stats | `test/perf/native_layout_performance_spec.spl` | 88 |
| 131 | TODO | general | P3 | Compile both versions | `test/perf/native_layout_performance_spec.spl` | 141 |
| 132 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 172 |
| 133 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 201 |
| 134 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 233 |
| 135 | TODO | general | P3 | Compile both and compare | `test/perf/native_layout_performance_spec.spl` | 267 |
| 136 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/perf/native_layout_performance_spec.spl` | 341 |
| 137 | TODO | general | P3 | Benchmark actual execution | `test/perf/native_layout_performance_spec.spl` | 368 |
| 138 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/perf/intensive/http/h3_settings_write_frame_spec.spl` | 13 |
| 139 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/compiler/parser_improvements_spec.spl` | 209 |
| 140 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/system/generated/spec_matchers_spec.spl` | 63 |
| 141 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 83 |
| 142 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 129 |
| 143 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 63 |
| 144 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 67 |
| 145 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 78 |
| 146 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 147 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 64 |
| 148 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 68 |
| 149 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 72 |
| 150 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_module_spec.spl` | 10 |
| 151 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 152 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_types_spec.spl` | 10 |
| 153 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 154 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/parser_spec.spl` | 209 |
| 155 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/01_unit/compiler/loader/jit_context_spec.spl` | 209 |
| 156 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 336 |
| 157 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/jit_context_spec.spl` | 388 |
| 158 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/jit_context_spec.spl` | 397 |
| 159 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/jit_context_spec.spl` | 401 |
| 160 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 405 |
| 161 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 409 |
| 162 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/01_unit/app/tooling/test_db_integrity_spec.spl` | 470 |
| 163 | TODO | general | P3 | Add memory profiling | `test/01_unit/app/tooling/test_db_performance_spec.spl` | 484 |
| 164 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 54 |
| 165 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 61 |
| 166 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 70 |
| 167 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 77 |
| 168 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 86 |
| 169 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 93 |
| 170 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 121 |
| 171 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 130 |
| 172 | TODO | general | P3 | Simulate write failure | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 137 |
| 173 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 146 |
| 174 | TODO | general | P3 | Implement after process spawning is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 155 |
| 175 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 55 |
| 176 | TODO | general | P3 | Test function compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 62 |
| 177 | TODO | general | P3 | Test class compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 69 |
| 178 | TODO | general | P3 | Test struct compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 76 |
| 179 | TODO | general | P3 | Test enum compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 80 |
| 180 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 96 |
| 181 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 103 |
| 182 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 110 |
| 183 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 114 |
| 184 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 118 |
| 185 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 134 |
| 186 | TODO | general | P3 | Test return type inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 138 |
| 187 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 142 |
| 188 | TODO | general | P3 | Test type error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 146 |
| 189 | TODO | general | P3 | Test recursive types | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 150 |
| 190 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 166 |
| 191 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 173 |
| 192 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 180 |
| 193 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 187 |
| 194 | TODO | general | P3 | Test error suggestions | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 191 |
| 195 | TODO | general | P3 | Test import resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 207 |
| 196 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 214 |
| 197 | TODO | general | P3 | Test circular import detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 218 |
| 198 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 225 |
| 199 | TODO | general | P3 | Test hot reload | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 229 |
| 200 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 245 |
| 201 | TODO | general | P3 | Test cache eviction | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 254 |
| 202 | TODO | general | P3 | Test refcount management | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 258 |
| 203 | TODO | general | P3 | Test leak detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 262 |
| 204 | TODO | general | P3 | Test deep recursion | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 266 |
| 205 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 206 | TODO | general | P3 | Implement actual ELF reading | `test/integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 207 | TODO | general | P3 | Implement actual symbol parsing | `test/integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 208 | TODO | general | P3 | Implement actual size measurement | `test/integration/compiler/native_backend_e2e_spec.spl` | 45 |
| 209 | TODO | general | P3 | Verify function order in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 131 |
| 210 | TODO | general | P3 | Verify actual ordering in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 164 |
| 211 | TODO | general | P3 | Verify relocations are correct | `test/integration/compiler/native_backend_e2e_spec.spl` | 293 |
| 212 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/integration/compiler/native_backend_e2e_spec.spl` | 375 |
| 213 | TODO | general | P3 | Create minimal MirModule and compile | `test/integration/compiler/llvm_backend_e2e_spec.spl` | 189 |
| 214 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_module_spec.spl` | 10 |
| 215 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 216 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_types_spec.spl` | 10 |
| 217 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 218 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/unit/compiler/frontend/parser_spec.spl` | 30 |
| 219 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/unit/compiler/loader/jit_context_spec.spl` | 209 |
| 220 | TODO | general | P3 | Add TypeRegistry validation | `test/unit/compiler/loader/jit_context_spec.spl` | 336 |
| 221 | TODO | general | P3 | Create test template and type args | `test/unit/compiler/loader/jit_context_spec.spl` | 388 |
| 222 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/unit/compiler/loader/jit_context_spec.spl` | 397 |
| 223 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/unit/compiler/loader/jit_context_spec.spl` | 401 |
| 224 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 405 |
| 225 | TODO | general | P3 | Verify DI container passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 409 |
| 226 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 246 |
| 227 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 258 |
| 228 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 270 |
| 229 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 282 |
| 230 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/unit/sffi/sffi_public_api_spec.spl` | 131 |
| 231 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/unit/app/tooling/test_db_integrity_spec.spl` | 468 |
| 232 | TODO | general | P3 | Add memory profiling | `test/unit/app/tooling/test_db_performance_spec.spl` | 496 |
| 233 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 51 |
| 234 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 58 |
| 235 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 67 |
| 236 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 74 |
| 237 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 83 |
| 238 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 90 |
| 239 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 118 |
| 240 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 127 |
| 241 | TODO | general | P3 | Simulate write failure | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 134 |
| 242 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 143 |
| 243 | TODO | general | P3 | Implement after process spawning is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 152 |
| 244 | TODO | general | P3 | bench_run_warm + bench_emit require cross-module struct construction | `test/05_perf/web/web_server_bench_spec.spl` | 206 |
| 245 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` | 345 |
| 246 | TODO | general | P3 | SMF loader currently cannot resolve time externs used in harness internals | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 169 |
| 247 | TODO | general | P3 | Enable once native compilation is confirmed stable in test runner. | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 177 |
| 248 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 181 |
| 249 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/native_layout_performance_spec.spl` | 52 |
| 250 | TODO | general | P3 | Parse output from time -v or perf stat | `test/05_perf/native_layout_performance_spec.spl` | 66 |
| 251 | TODO | general | P3 | Compile source | `test/05_perf/native_layout_performance_spec.spl` | 75 |
| 252 | TODO | general | P3 | Use file stats | `test/05_perf/native_layout_performance_spec.spl` | 94 |
| 253 | TODO | general | P3 | Compile both versions | `test/05_perf/native_layout_performance_spec.spl` | 152 |
| 254 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 185 |
| 255 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 216 |
| 256 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 250 |
| 257 | TODO | general | P3 | Compile both and compare | `test/05_perf/native_layout_performance_spec.spl` | 286 |
| 258 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/native_layout_performance_spec.spl` | 366 |
| 259 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/native_layout_performance_spec.spl` | 395 |
| 260 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/05_perf/intensive/http/h3_settings_write_frame_spec.spl` | 17 |
| 261 | TODO | general | P3 | admit SFFI providers with artifact-bound evidence | `doc/08_tracking/todo/sffi_v2_provider_admission_2026-08-27.md` | 1 |
| 262 | TODO | general | P3 | hardening plan — resume after the bootstrap seed redeploy is stable | `doc/08_tracking/todo/hardening_resume_after_seed_redeploy_2026-08-25.md` | 1 |
| 263 | TODO | general | P3 | the workspace root guard cannot fail in CI (vacuous gate) | `doc/08_tracking/todo/workspace_root_guard_is_vacuous_in_ci_2026-07-28.md` | 1 |
| 264 | TODO | infra | P3 | Build the native HTTPServer benchmark gate scripts or drop the claim | `doc/08_tracking/todo/native_httpserver_benchmark_gate_scripts_missing_2026-08-08.md` | 18 |
| 265 | TODO | general | P3 | Route dynamic manifest passes to a real execution path | `doc/08_tracking/todo/optimizer_manifest_dynamic_pass_routing_2026-08-18.md` | 1 |
| 266 | TODO | spipe_docgen | P2 | Render per-cell `%%mode` lane badges in notebook spec manuals | `doc/08_tracking/todo/spipe_docgen_lane_badges_2026-08-08.md` | 5 |
| 267 | TODO | general | P3 | std.async.runtime cannot wake clock-based (timer/sleep) futures | `doc/08_tracking/todo/async_runtime_timer_wakeup_for_sleep_2026-08-17.md` | 1 |
| 268 | TODO | general | P3 | bind protected DBFS objects to production descriptor owners | `doc/08_tracking/todo/server_data_namespace_fd_binding_v1.md` | 1 |
| 269 | TODO | test | P2 | Build (or restore) the Jupyter full-server and notebook-exec E2E helpers | `doc/08_tracking/todo/jupyter_e2e_helper_scripts_missing_2026-08-08.md` | 15 |
| 270 | TODO | general | P3 | test_runner_execute -> composite -> gpu_lane eager imports cost ~40s of seed-interpreter load | `doc/08_tracking/todo/test_runner_execute_composite_gpu_eager_import_cost_2026-08-17.md` | 1 |
| 271 | TODO | sspec-maintain | P1 | Enhance scoring rules to recognize lane-gated notebook specs | `doc/08_tracking/todo/sspec_maintain_lane_aware_scoring_2026-08-08.md` | 5 |
| 272 | TODO | bootstrap | P2 | Build `scripts/bootstrap/rollback-bootstrap-deploy.shs` | `doc/08_tracking/todo/rollback_bootstrap_deploy_script_missing_2026-08-08.md` | 11 |
| 273 | TODO | uno_q | P2 | POSTPONED until an Arduino UNO Q and debug access are available: run supplementary QRB2210 AArch64 and STM32U585 build/UART checks without claiming Cosmos hardware acceptance. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 16 |
| 274 | TODO | cosmos | P0 | POSTPONED until identified Cosmos+ hardware and lab fixtures are available: execute and retain BT-001 through BT-006. The 2026-07-29 host audit found a Xilinx ML Carrier FT4232H (`XFL1OSWWFM2B`), a Lauterbach PODBUS controller, and three Samsung NVMe devices, but no Cosmos+/OpenSSD PCIe device. The repo-managed TRACE32 server reached TCP 20000, while read-only CPU, system, and `STATE.RUN()` queries all failed with exit 8128 because no target was configured. | `doc/08_tracking/todo/cosmos_nvme_firmware_remaining_2026-07-28.md` | 17 |
| 275 | TODO | general | P3 | SOSIX runtime unification — blocked rows (resume conditions) | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 1 |
| 276 | TODO | general | P3 | (sosix F1) land the GPU G1 proxy storage slice on a host with a real GPU and a deployed pure-Simple binary; resume via doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md lanes B/C | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 37 |
| 277 | TODO | general | P3 | (sosix AC-3b) prove the QEMU serial row with observed bytes once a pure-Simple compiler accepted by simple_binary_is_valid is deployed; publish via produce-sosix-qemu-native-pass-bundle.shs and import via collect-sosix-qemu-evidence.shs | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 39 |
| 278 | TODO | general | P3 | (sosix G4) implement the SimpleOS device-initiated queues GQ-001..012 after the GQ-001 native capability report on real hardware | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 41 |
| 279 | TODO | general | P3 | (sosix startup-ab) re-run check-startup-size-performance-audit.shs on a host where its Simple probe rows do not exit 127, and diff against doc/09_report/startup_size_performance_audit_2026-05-27.md | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 43 |
| 280 | TODO | general | P3 | (sosix A5) drop the no-rename constraint on the src/os/sosix/core shims once aliased constant imports stop yielding 0; the row's original wording (a parse error in `export use ... as`) was wrong — measured 2026-09-06, `use m.{CONST as ALIAS}` binds and silently yields 0 for u8 and u32 alike while aliased functions are fine, see doc/08_tracking/bug/aliased_constant_import_silently_yields_zero_2026-09-06.md | `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md` | 45 |
| 281 | TODO | general | P3 | (simpleorch container) BLOCKED — implement and prove the Linux OCI native-container provider with PODMAN as the default engine; unblock with `apt install podman uidmap` plus lifting `kernel.apparmor_restrict_unprivileged_userns`, or fall back to `usermod -aG docker` | `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md` | 1 |
| 282 | TODO | general | P3 | (simpleorch container-oci) implement RuntimeProviderV1 create/start/wait/stop/destroy/recover for the Linux OCI lane; blocked on host privilege above, resume command in this file | `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md` | 106 |
| 283 | TODO | general | P3 | (simpleorch container-evidence) flip the native-container receipts in test/02_integration/app/ci/pipeline_runner_spec.spl from VERDICT_BLOCKED to a real container receipt (attempt 1, run nonce in stdout) once the lane is unblocked | `doc/08_tracking/todo/simple_orchestrator_native_container_lane_blocked_2026-09-07.md` | 107 |
| 284 | TODO | rendering | P0 | BLOCKED: run the four-lane QEMU/container Vulkan mission showcase with an admitted self-hosted CLI, producer receipts, and an allocation-cap receipt; see TODO DB row 277 and this plan's resume command. | `doc/03_plan/sys_test/render_lane_mission_showcase.md` | 53 |
