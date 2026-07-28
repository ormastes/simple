# TODO Tracking

**Total:** 312 items | **Open:** 312 | **Blocked:** 0

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 0 |
| P1 | 0 |
| P2 | 0 |
| P3 | 312 |

## By Area

| Area | Count |
|------|-------|
| general | 312 |

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `src/compiler/80.driver/watcher/watcher_daemon.spl` | 70 |
| 1 | TODO | general | P3 | wire up hwprobe when available | `src/compiler/30.types/simd_capabilities.spl` | 349 |
| 2 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `src/app/devhub/cmd_daily_debug.spl` | 159 |
| 3 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 4 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 5 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 6 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 7 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 8 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 9 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 10 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `src/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 11 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 12 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 13 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 14 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 15 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 16 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 17 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 18 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 19 | TODO | general | P3 | lower to csrs in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 20 | TODO | general | P3 | lower to csrc in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 21 | TODO | general | P3 | lower to csrrw in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 22 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `src/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 23 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 24 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 25 | TODO | general | P3 | Implement ValueBuilder and complete handler integration | `src/compiler_rust/lib/std/src/sdn/handler.spl` | 205 |
| 26 | TODO | general | P3 | add more about copy-paste and human readability. | `src/compiler_rust/vendor/shlex/src/quoting_warning.md` | 365 |
| 27 | TODO | general | P3 | when netstack is wired, call net_service_poll() here to drive | `src/os/kernel/net/driver_shim.spl` | 337 |
| 28 | TODO | general | P3 | Enable tests once native codegen is complete | `test/01_unit/compiler/codegen/static_method_spec.spl` | 337 |
| 29 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 30 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 31 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_module_spec.spl` | 10 |
| 32 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_types_spec.spl` | 10 |
| 33 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 209 |
| 34 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 336 |
| 35 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 388 |
| 36 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 397 |
| 37 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 401 |
| 38 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 405 |
| 39 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 409 |
| 40 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/01_unit/compiler/loader/jit_context_spec.spl` | 209 |
| 41 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 336 |
| 42 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/jit_context_spec.spl` | 388 |
| 43 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/jit_context_spec.spl` | 397 |
| 44 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/jit_context_spec.spl` | 401 |
| 45 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 405 |
| 46 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 409 |
| 47 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/.spipe_matchers_parser_spec.spl` | 30 |
| 48 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/parser_spec.spl` | 49 |
| 49 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 42 |
| 50 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 47 |
| 51 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 54 |
| 52 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 59 |
| 53 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 66 |
| 54 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 71 |
| 55 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 95 |
| 56 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 102 |
| 57 | TODO | general | P3 | Simulate write failure | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 107 |
| 58 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 114 |
| 59 | TODO | general | P3 | Implement after process spawning is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 121 |
| 60 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/01_unit/app/tooling/.spipe_matchers_test_db_integrity_spec.spl` | 427 |
| 61 | TODO | general | P3 | Add memory profiling | `test/01_unit/app/tooling/.spipe_matchers_test_db_performance_spec.spl` | 467 |
| 62 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 42 |
| 63 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 47 |
| 64 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 54 |
| 65 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 59 |
| 66 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 66 |
| 67 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 71 |
| 68 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 95 |
| 69 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 102 |
| 70 | TODO | general | P3 | Simulate write failure | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 107 |
| 71 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 114 |
| 72 | TODO | general | P3 | Implement after process spawning is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 121 |
| 73 | TODO | general | P3 | Add memory profiling | `test/01_unit/app/tooling/test_db_performance_spec.spl` | 467 |
| 74 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/01_unit/app/tooling/test_db_integrity_spec.spl` | 427 |
| 75 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 246 |
| 76 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 258 |
| 77 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 270 |
| 78 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 282 |
| 79 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/01_unit/sffi_standalone/.spipe_matchers_sffi_public_api_spec.spl` | 112 |
| 80 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/.spipe_matchers_llvm_backend_e2e_spec.spl` | 149 |
| 81 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 20 |
| 82 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 26 |
| 83 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 32 |
| 84 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 38 |
| 85 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 117 |
| 86 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 148 |
| 87 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 269 |
| 88 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 345 |
| 89 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 12 |
| 90 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 18 |
| 91 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 24 |
| 92 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 30 |
| 93 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 119 |
| 94 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 150 |
| 95 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 271 |
| 96 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 347 |
| 97 | TODO | general | P3 | Implement when parser integration complete | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 54 |
| 98 | TODO | general | P3 | Test function compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 61 |
| 99 | TODO | general | P3 | Test class compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 68 |
| 100 | TODO | general | P3 | Test struct compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 75 |
| 101 | TODO | general | P3 | Test enum compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 79 |
| 102 | TODO | general | P3 | Test cross-module method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 95 |
| 103 | TODO | general | P3 | Test generic method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 102 |
| 104 | TODO | general | P3 | Test trait method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 109 |
| 105 | TODO | general | P3 | Test UFCS resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 113 |
| 106 | TODO | general | P3 | Test ambiguity detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 117 |
| 107 | TODO | general | P3 | Test type inference for val bindings | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 133 |
| 108 | TODO | general | P3 | Test return type inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 137 |
| 109 | TODO | general | P3 | Test generic type argument inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 141 |
| 110 | TODO | general | P3 | Test type error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 145 |
| 111 | TODO | general | P3 | Test recursive types | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 149 |
| 112 | TODO | general | P3 | Test parse error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 165 |
| 113 | TODO | general | P3 | Test compilation error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 172 |
| 114 | TODO | general | P3 | Test runtime error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 179 |
| 115 | TODO | general | P3 | Test span/location in errors | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 186 |
| 116 | TODO | general | P3 | Test error suggestions | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 190 |
| 117 | TODO | general | P3 | Test import resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 206 |
| 118 | TODO | general | P3 | Test private symbol hiding | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 213 |
| 119 | TODO | general | P3 | Test circular import detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 217 |
| 120 | TODO | general | P3 | Test dependency graph resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 224 |
| 121 | TODO | general | P3 | Test hot reload | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 228 |
| 122 | TODO | general | P3 | Test scope cleanup | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 244 |
| 123 | TODO | general | P3 | Test cache eviction | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 253 |
| 124 | TODO | general | P3 | Test refcount management | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 257 |
| 125 | TODO | general | P3 | Test leak detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 261 |
| 126 | TODO | general | P3 | Test deep recursion | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 265 |
| 127 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/llvm_backend_e2e_spec.spl` | 149 |
| 128 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 20 |
| 129 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 27 |
| 130 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 131 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 132 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 118 |
| 133 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 149 |
| 134 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 270 |
| 135 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 346 |
| 136 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 68 |
| 137 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 108 |
| 138 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/compiler/parser_improvements_spec.spl` | 180 |
| 139 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 33 |
| 140 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 74 |
| 141 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 83 |
| 142 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 92 |
| 143 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 117 |
| 144 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 134 |
| 145 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/03_system/feature/usage/macro_validation_spec.spl` | 183 |
| 146 | TODO | general | P3 | Lambda default parameters not yet supported | `test/03_system/feature/usage/parser_default_keyword_spec.spl` | 146 |
| 147 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/03_system/feature/usage/primitive_types_spec.spl` | 61 |
| 148 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/03_system/feature/usage/set_literal_spec.spl` | 33 |
| 149 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/03_system/feature/usage/set_literal_spec.spl` | 74 |
| 150 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 83 |
| 151 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 92 |
| 152 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 117 |
| 153 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 134 |
| 154 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/03_system/feature/usage/trait_coherence_spec.spl` | 342 |
| 155 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1027 |
| 156 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1032 |
| 157 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1037 |
| 158 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1042 |
| 159 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1051 |
| 160 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1056 |
| 161 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1061 |
| 162 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1066 |
| 163 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 68 |
| 164 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 72 |
| 165 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 83 |
| 166 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 87 |
| 167 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 63 |
| 168 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 67 |
| 169 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 78 |
| 170 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 171 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 64 |
| 172 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 68 |
| 173 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 72 |
| 174 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/03_system/generated/spec_matchers_spec.spl` | 63 |
| 175 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/05_perf/intensive/http/.spipe_matchers_h3_settings_write_frame_spec.spl` | 13 |
| 176 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/05_perf/intensive/http/h3_settings_write_frame_spec.spl` | 13 |
| 177 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 46 |
| 178 | TODO | general | P3 | Parse output from time -v or perf stat | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 60 |
| 179 | TODO | general | P3 | Compile source | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 69 |
| 180 | TODO | general | P3 | Use file stats | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 88 |
| 181 | TODO | general | P3 | Compile both versions | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 141 |
| 182 | TODO | general | P3 | Compile and measure | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 172 |
| 183 | TODO | general | P3 | Compile and measure | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 201 |
| 184 | TODO | general | P3 | Compile and measure | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 233 |
| 185 | TODO | general | P3 | Compile both and compare | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 267 |
| 186 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 341 |
| 187 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 368 |
| 188 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/db/.spipe_wrapped_entry_db_ram_vs_persistent_bench_spec.spl` | 400 |
| 189 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` | 340 |
| 190 | TODO | general | P3 | SMF loader currently cannot resolve time externs used in harness internals | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 164 |
| 191 | TODO | general | P3 | Enable once native compilation is confirmed stable in test runner. | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 172 |
| 192 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 176 |
| 193 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/native_layout_performance_spec.spl` | 46 |
| 194 | TODO | general | P3 | Parse output from time -v or perf stat | `test/05_perf/native_layout_performance_spec.spl` | 60 |
| 195 | TODO | general | P3 | Compile source | `test/05_perf/native_layout_performance_spec.spl` | 69 |
| 196 | TODO | general | P3 | Use file stats | `test/05_perf/native_layout_performance_spec.spl` | 88 |
| 197 | TODO | general | P3 | Compile both versions | `test/05_perf/native_layout_performance_spec.spl` | 141 |
| 198 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 172 |
| 199 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 201 |
| 200 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 233 |
| 201 | TODO | general | P3 | Compile both and compare | `test/05_perf/native_layout_performance_spec.spl` | 267 |
| 202 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/native_layout_performance_spec.spl` | 341 |
| 203 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/native_layout_performance_spec.spl` | 368 |
| 204 | TODO | general | P3 | bench_run_warm + bench_emit require cross-module struct construction | `test/05_perf/web/web_server_bench_spec.spl` | 187 |
| 205 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 54 |
| 206 | TODO | general | P3 | Test function compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 61 |
| 207 | TODO | general | P3 | Test class compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 68 |
| 208 | TODO | general | P3 | Test struct compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 75 |
| 209 | TODO | general | P3 | Test enum compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 79 |
| 210 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 95 |
| 211 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 102 |
| 212 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 109 |
| 213 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 113 |
| 214 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 117 |
| 215 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 133 |
| 216 | TODO | general | P3 | Test return type inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 137 |
| 217 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 141 |
| 218 | TODO | general | P3 | Test type error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 145 |
| 219 | TODO | general | P3 | Test recursive types | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 149 |
| 220 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 165 |
| 221 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 172 |
| 222 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 179 |
| 223 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 186 |
| 224 | TODO | general | P3 | Test error suggestions | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 190 |
| 225 | TODO | general | P3 | Test import resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 206 |
| 226 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 213 |
| 227 | TODO | general | P3 | Test circular import detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 217 |
| 228 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 224 |
| 229 | TODO | general | P3 | Test hot reload | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 228 |
| 230 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 244 |
| 231 | TODO | general | P3 | Test cache eviction | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 253 |
| 232 | TODO | general | P3 | Test refcount management | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 257 |
| 233 | TODO | general | P3 | Test leak detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 261 |
| 234 | TODO | general | P3 | Test deep recursion | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 265 |
| 235 | TODO | general | P3 | Create minimal MirModule and compile | `test/integration/compiler/llvm_backend_e2e_spec.spl` | 149 |
| 236 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/integration/compiler/native_backend_e2e_spec.spl` | 20 |
| 237 | TODO | general | P3 | Implement actual ELF reading | `test/integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 238 | TODO | general | P3 | Implement actual symbol parsing | `test/integration/compiler/native_backend_e2e_spec.spl` | 32 |
| 239 | TODO | general | P3 | Implement actual size measurement | `test/integration/compiler/native_backend_e2e_spec.spl` | 38 |
| 240 | TODO | general | P3 | Verify function order in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 117 |
| 241 | TODO | general | P3 | Verify actual ordering in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 148 |
| 242 | TODO | general | P3 | Verify relocations are correct | `test/integration/compiler/native_backend_e2e_spec.spl` | 269 |
| 243 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/integration/compiler/native_backend_e2e_spec.spl` | 345 |
| 244 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 42 |
| 245 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 47 |
| 246 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 54 |
| 247 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 59 |
| 248 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 66 |
| 249 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 71 |
| 250 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 95 |
| 251 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 102 |
| 252 | TODO | general | P3 | Simulate write failure | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 107 |
| 253 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 114 |
| 254 | TODO | general | P3 | Implement after process spawning is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 121 |
| 255 | TODO | general | P3 | Add memory profiling | `test/unit/app/tooling/test_db_performance_spec.spl` | 467 |
| 256 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/unit/app/tooling/test_db_integrity_spec.spl` | 427 |
| 257 | TODO | general | P3 | Enable tests once native codegen is complete | `test/unit/compiler/codegen/static_method_spec.spl` | 337 |
| 258 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/unit/compiler/frontend/parser_spec.spl` | 30 |
| 259 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 260 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 261 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_module_spec.spl` | 10 |
| 262 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_types_spec.spl` | 10 |
| 263 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/unit/compiler/loader/jit_context_spec.spl` | 209 |
| 264 | TODO | general | P3 | Add TypeRegistry validation | `test/unit/compiler/loader/jit_context_spec.spl` | 336 |
| 265 | TODO | general | P3 | Create test template and type args | `test/unit/compiler/loader/jit_context_spec.spl` | 388 |
| 266 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/unit/compiler/loader/jit_context_spec.spl` | 397 |
| 267 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/unit/compiler/loader/jit_context_spec.spl` | 401 |
| 268 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 405 |
| 269 | TODO | general | P3 | Verify DI container passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 409 |
| 270 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 246 |
| 271 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 258 |
| 272 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 270 |
| 273 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 282 |
| 274 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/unit/sffi/sffi_public_api_spec.spl` | 112 |
| 275 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/perf/intensive/http/h3_settings_write_frame_spec.spl` | 13 |
| 276 | TODO | general | P3 | Execute binary and wait for completion | `test/perf/native_layout_performance_spec.spl` | 46 |
| 277 | TODO | general | P3 | Parse output from time -v or perf stat | `test/perf/native_layout_performance_spec.spl` | 60 |
| 278 | TODO | general | P3 | Compile source | `test/perf/native_layout_performance_spec.spl` | 69 |
| 279 | TODO | general | P3 | Use file stats | `test/perf/native_layout_performance_spec.spl` | 88 |
| 280 | TODO | general | P3 | Compile both versions | `test/perf/native_layout_performance_spec.spl` | 141 |
| 281 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 172 |
| 282 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 201 |
| 283 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 233 |
| 284 | TODO | general | P3 | Compile both and compare | `test/perf/native_layout_performance_spec.spl` | 267 |
| 285 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/perf/native_layout_performance_spec.spl` | 341 |
| 286 | TODO | general | P3 | Benchmark actual execution | `test/perf/native_layout_performance_spec.spl` | 368 |
| 287 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/compiler/parser_improvements_spec.spl` | 170 |
| 288 | TODO | general | P3 | Implement conditional rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 68 |
| 289 | TODO | general | P3 | Implement conditional rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 72 |
| 290 | TODO | general | P3 | Implement list rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 83 |
| 291 | TODO | general | P3 | Implement list rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 87 |
| 292 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 63 |
| 293 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 67 |
| 294 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 78 |
| 295 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 296 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 64 |
| 297 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 68 |
| 298 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 72 |
| 299 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/system/generated/spec_matchers_spec.spl` | 63 |
| 300 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 68 |
| 301 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 108 |
| 302 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/feature/usage/macro_validation_spec.spl` | 183 |
| 303 | TODO | general | P3 | Lambda default parameters not yet supported | `test/feature/usage/parser_default_keyword_spec.spl` | 146 |
| 304 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/feature/usage/primitive_types_spec.spl` | 61 |
| 305 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/feature/usage/set_literal_spec.spl` | 33 |
| 306 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/feature/usage/set_literal_spec.spl` | 74 |
| 307 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 83 |
| 308 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 92 |
| 309 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 117 |
| 310 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 134 |
| 311 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/feature/usage/trait_coherence_spec.spl` | 342 |
