# TODO Tracking

**Total:** 528 items | **Open:** 528 | **Blocked:** 0

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 0 |
| P1 | 7 |
| P2 | 21 |
| P3 | 500 |

## By Area

| Area | Count |
|------|-------|
| runtime | 7 |
| interpreter | 7 |
| general | 500 |
| quic-server | 7 |
| stdlib | 7 |

## P1 High Priority

- [TODO] Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. - `src/lib/nogc_sync_mut/io/signature_sffi.spl:129`
- [TODO] Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. - `src/std/nogc_sync_mut/io/signature_sffi.spl:129`
- [TODO] Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. - `test/01_unit/compiler/std/nogc_sync_mut/io/signature_sffi.spl:129`
- [TODO] Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. - `test/01_unit/lib/database/lib/nogc_sync_mut/io/signature_sffi.spl:129`
- [TODO] Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. - `test/unit/lib/database/lib/nogc_sync_mut/io/signature_sffi.spl:129`
- [TODO] Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. - `test/unit/compiler/std/nogc_sync_mut/io/signature_sffi.spl:129`
- [TODO] Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. - `test/feature/lib/lib/nogc_sync_mut/io/signature_sffi.spl:129`

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `src/compiler/80.driver/watcher/watcher_daemon.spl` | 70 |
| 1 | TODO | general | P3 | wire up hwprobe when available | `src/compiler/30.types/simd_capabilities.spl` | 349 |
| 2 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `src/compiler/driver/watcher/watcher_daemon.spl` | 70 |
| 3 | TODO | general | P3 | wire up hwprobe when available | `src/compiler/types/simd_capabilities.spl` | 349 |
| 4 | TODO | general | P3 | Import bugdb handlers when available | `src/app/mcp/bootstrap/main_optimized.spl` | 240 |
| 5 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `src/app/itf/cmd_daily_debug.spl` | 159 |
| 6 | TODO | interpreter | P1 | Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. | `src/lib/nogc_sync_mut/io/signature_sffi.spl` | 129 |
| 7 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 8 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 9 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 10 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 11 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `src/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 12 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 13 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 14 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 15 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 16 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 17 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 18 | TODO | general | P3 | Integrate Simple interpreter here | `src/lib/gc_async_mut/gpu/browser_engine/script/simple_script.spl` | 62 |
| 19 | TODO | runtime | P2 | Interpreter loses the `self` binding when a struct | `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` | 1304 |
| 20 | TODO | quic-server | P2 | wire transport-level send queue | `src/lib/nogc_async_mut/io/quic/quic_server.spl` | 288 |
| 21 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `src/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 22 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 23 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 24 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 25 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 26 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 27 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 28 | TODO | stdlib | P2 | extract ALPN from handshake state when ALPN is implemented | `src/lib/nogc_async_mut/http_server/worker.spl` | 348 |
| 29 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 30 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 31 | TODO | general | P3 | lower to csrs in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 32 | TODO | general | P3 | lower to csrc in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 33 | TODO | general | P3 | lower to csrrw in compiled mode | `src/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 34 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `src/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 35 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 36 | TODO | general | P3 | support packed delta stream format | `src/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 37 | TODO | general | P3 | Implement ValueBuilder and complete handler integration | `src/compiler_rust/lib/std/src/sdn/handler.spl` | 205 |
| 38 | TODO | general | P3 | add more about copy-paste and human readability. | `src/compiler_rust/vendor/shlex/src/quoting_warning.md` | 365 |
| 39 | TODO | general | P3 | when netstack is wired, call net_service_poll() here to drive | `src/os/kernel/net/driver_shim.spl` | 337 |
| 40 | TODO | interpreter | P1 | Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. | `src/std/nogc_sync_mut/io/signature_sffi.spl` | 129 |
| 41 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `src/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 42 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `src/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 43 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `src/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 44 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `src/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 45 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `src/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 46 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/std/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 47 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/std/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 48 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 49 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 50 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 51 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 52 | TODO | general | P3 | Integrate Simple interpreter here | `src/std/gc_async_mut/gpu/browser_engine/script/simple_script.spl` | 62 |
| 53 | TODO | runtime | P2 | Interpreter loses the `self` binding when a struct | `src/std/gc_async_mut/gpu/engine2d/backend_metal.spl` | 1304 |
| 54 | TODO | quic-server | P2 | wire transport-level send queue | `src/std/nogc_async_mut/io/quic/quic_server.spl` | 288 |
| 55 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `src/std/nogc_async_mut/gpu/memory.spl` | 244 |
| 56 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `src/std/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 57 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `src/std/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 58 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `src/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 59 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `src/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 60 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `src/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 61 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `src/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 62 | TODO | stdlib | P2 | extract ALPN from handshake state when ALPN is implemented | `src/std/nogc_async_mut/http_server/worker.spl` | 348 |
| 63 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `src/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 64 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `src/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 65 | TODO | general | P3 | lower to csrs in compiled mode | `src/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 66 | TODO | general | P3 | lower to csrc in compiled mode | `src/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 67 | TODO | general | P3 | lower to csrrw in compiled mode | `src/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 68 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `src/std/skia/bridge/engine2d_bridge.spl` | 125 |
| 69 | TODO | general | P3 | support packed delta stream format | `src/std/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 70 | TODO | general | P3 | support packed delta stream format | `src/std/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 71 | TODO | general | P3 | Enable tests once native codegen is complete | `test/01_unit/compiler/codegen/static_method_spec.spl` | 337 |
| 72 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 73 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 74 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_module_spec.spl` | 10 |
| 75 | TODO | general | P3 | Enable when hir module is ready for import | `test/01_unit/compiler/hir/hir_types_spec.spl` | 10 |
| 76 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 209 |
| 77 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 336 |
| 78 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 388 |
| 79 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 397 |
| 80 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 401 |
| 81 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 405 |
| 82 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/.spipe_matchers_jit_context_spec.spl` | 409 |
| 83 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/01_unit/compiler/loader/jit_context_spec.spl` | 209 |
| 84 | TODO | general | P3 | Add TypeRegistry validation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 336 |
| 85 | TODO | general | P3 | Create test template and type args | `test/01_unit/compiler/loader/jit_context_spec.spl` | 388 |
| 86 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/01_unit/compiler/loader/jit_context_spec.spl` | 397 |
| 87 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/01_unit/compiler/loader/jit_context_spec.spl` | 401 |
| 88 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 405 |
| 89 | TODO | general | P3 | Verify DI container passed to compilation | `test/01_unit/compiler/loader/jit_context_spec.spl` | 409 |
| 90 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/.spipe_matchers_parser_spec.spl` | 30 |
| 91 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/01_unit/compiler/frontend/parser_spec.spl` | 49 |
| 92 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `test/01_unit/compiler/compiler/80.driver/watcher/watcher_daemon.spl` | 70 |
| 93 | TODO | general | P3 | wire up hwprobe when available | `test/01_unit/compiler/compiler/30.types/simd_capabilities.spl` | 349 |
| 94 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `test/01_unit/compiler/compiler/driver/watcher/watcher_daemon.spl` | 70 |
| 95 | TODO | general | P3 | wire up hwprobe when available | `test/01_unit/compiler/compiler/types/simd_capabilities.spl` | 349 |
| 96 | TODO | interpreter | P1 | Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. | `test/01_unit/compiler/std/nogc_sync_mut/io/signature_sffi.spl` | 129 |
| 97 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `test/01_unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 98 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `test/01_unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 99 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `test/01_unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 100 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `test/01_unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 101 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `test/01_unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 102 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/01_unit/compiler/std/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 103 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/01_unit/compiler/std/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 104 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/01_unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 105 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/01_unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 106 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/01_unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 107 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/01_unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 108 | TODO | general | P3 | Integrate Simple interpreter here | `test/01_unit/compiler/std/gc_async_mut/gpu/browser_engine/script/simple_script.spl` | 62 |
| 109 | TODO | runtime | P2 | Interpreter loses the `self` binding when a struct | `test/01_unit/compiler/std/gc_async_mut/gpu/engine2d/backend_metal.spl` | 1304 |
| 110 | TODO | quic-server | P2 | wire transport-level send queue | `test/01_unit/compiler/std/nogc_async_mut/io/quic/quic_server.spl` | 288 |
| 111 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `test/01_unit/compiler/std/nogc_async_mut/gpu/memory.spl` | 244 |
| 112 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/01_unit/compiler/std/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 113 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/01_unit/compiler/std/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 114 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/01_unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 115 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/01_unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 116 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/01_unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 117 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/01_unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 118 | TODO | stdlib | P2 | extract ALPN from handshake state when ALPN is implemented | `test/01_unit/compiler/std/nogc_async_mut/http_server/worker.spl` | 348 |
| 119 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `test/01_unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 120 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `test/01_unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 121 | TODO | general | P3 | lower to csrs in compiled mode | `test/01_unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 122 | TODO | general | P3 | lower to csrc in compiled mode | `test/01_unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 123 | TODO | general | P3 | lower to csrrw in compiled mode | `test/01_unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 124 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `test/01_unit/compiler/std/skia/bridge/engine2d_bridge.spl` | 125 |
| 125 | TODO | general | P3 | support packed delta stream format | `test/01_unit/compiler/std/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 126 | TODO | general | P3 | support packed delta stream format | `test/01_unit/compiler/std/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 127 | TODO | general | P3 | Import bugdb handlers when available | `test/01_unit/app/desugar/app/mcp/bootstrap/main_optimized.spl` | 240 |
| 128 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `test/01_unit/app/desugar/app/itf/cmd_daily_debug.spl` | 159 |
| 129 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 42 |
| 130 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 47 |
| 131 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 54 |
| 132 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 59 |
| 133 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 66 |
| 134 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 71 |
| 135 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 95 |
| 136 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 102 |
| 137 | TODO | general | P3 | Simulate write failure | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 107 |
| 138 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 114 |
| 139 | TODO | general | P3 | Implement after process spawning is verified | `test/01_unit/app/tooling/.spipe_matchers_test_db_concurrency_spec.spl` | 121 |
| 140 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/01_unit/app/tooling/.spipe_matchers_test_db_integrity_spec.spl` | 427 |
| 141 | TODO | general | P3 | Add memory profiling | `test/01_unit/app/tooling/.spipe_matchers_test_db_performance_spec.spl` | 467 |
| 142 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 42 |
| 143 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 47 |
| 144 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 54 |
| 145 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 59 |
| 146 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 66 |
| 147 | TODO | general | P3 | Implement after FileLock API is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 71 |
| 148 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 95 |
| 149 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 102 |
| 150 | TODO | general | P3 | Simulate write failure | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 107 |
| 151 | TODO | general | P3 | Implement after isolated DB path support | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 114 |
| 152 | TODO | general | P3 | Implement after process spawning is verified | `test/01_unit/app/tooling/test_db_concurrency_spec.spl` | 121 |
| 153 | TODO | general | P3 | Add memory profiling | `test/01_unit/app/tooling/test_db_performance_spec.spl` | 467 |
| 154 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/01_unit/app/tooling/test_db_integrity_spec.spl` | 427 |
| 155 | TODO | interpreter | P1 | Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. | `test/01_unit/lib/database/lib/nogc_sync_mut/io/signature_sffi.spl` | 129 |
| 156 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 157 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 158 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 159 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 160 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 161 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 162 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 163 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 164 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 165 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 166 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/01_unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 167 | TODO | general | P3 | Integrate Simple interpreter here | `test/01_unit/lib/database/lib/gc_async_mut/gpu/browser_engine/script/simple_script.spl` | 62 |
| 168 | TODO | runtime | P2 | Interpreter loses the `self` binding when a struct | `test/01_unit/lib/database/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` | 1304 |
| 169 | TODO | quic-server | P2 | wire transport-level send queue | `test/01_unit/lib/database/lib/nogc_async_mut/io/quic/quic_server.spl` | 288 |
| 170 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `test/01_unit/lib/database/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 171 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/01_unit/lib/database/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 172 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/01_unit/lib/database/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 173 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/01_unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 174 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/01_unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 175 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/01_unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 176 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/01_unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 177 | TODO | stdlib | P2 | extract ALPN from handshake state when ALPN is implemented | `test/01_unit/lib/database/lib/nogc_async_mut/http_server/worker.spl` | 348 |
| 178 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `test/01_unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 179 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `test/01_unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 180 | TODO | general | P3 | lower to csrs in compiled mode | `test/01_unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 181 | TODO | general | P3 | lower to csrc in compiled mode | `test/01_unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 182 | TODO | general | P3 | lower to csrrw in compiled mode | `test/01_unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 183 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `test/01_unit/lib/database/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 184 | TODO | general | P3 | support packed delta stream format | `test/01_unit/lib/database/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 185 | TODO | general | P3 | support packed delta stream format | `test/01_unit/lib/database/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 186 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 246 |
| 187 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 258 |
| 188 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 270 |
| 189 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/01_unit/rtl/rtl/.spipe_matchers_encode_riscv_spec.spl` | 282 |
| 190 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/01_unit/sffi_standalone/.spipe_matchers_sffi_public_api_spec.spl` | 112 |
| 191 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/.spipe_matchers_llvm_backend_e2e_spec.spl` | 149 |
| 192 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 20 |
| 193 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 26 |
| 194 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 32 |
| 195 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 38 |
| 196 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 117 |
| 197 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 148 |
| 198 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 269 |
| 199 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/.spipe_matchers_native_backend_e2e_spec.spl` | 345 |
| 200 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 12 |
| 201 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 18 |
| 202 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 24 |
| 203 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 30 |
| 204 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 119 |
| 205 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 150 |
| 206 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 271 |
| 207 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/.spipe_wrapped_entry_native_backend_e2e_spec.spl` | 347 |
| 208 | TODO | general | P3 | Implement when parser integration complete | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 54 |
| 209 | TODO | general | P3 | Test function compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 61 |
| 210 | TODO | general | P3 | Test class compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 68 |
| 211 | TODO | general | P3 | Test struct compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 75 |
| 212 | TODO | general | P3 | Test enum compilation | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 79 |
| 213 | TODO | general | P3 | Test cross-module method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 95 |
| 214 | TODO | general | P3 | Test generic method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 102 |
| 215 | TODO | general | P3 | Test trait method resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 109 |
| 216 | TODO | general | P3 | Test UFCS resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 113 |
| 217 | TODO | general | P3 | Test ambiguity detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 117 |
| 218 | TODO | general | P3 | Test type inference for val bindings | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 133 |
| 219 | TODO | general | P3 | Test return type inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 137 |
| 220 | TODO | general | P3 | Test generic type argument inference | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 141 |
| 221 | TODO | general | P3 | Test type error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 145 |
| 222 | TODO | general | P3 | Test recursive types | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 149 |
| 223 | TODO | general | P3 | Test parse error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 165 |
| 224 | TODO | general | P3 | Test compilation error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 172 |
| 225 | TODO | general | P3 | Test runtime error reporting | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 179 |
| 226 | TODO | general | P3 | Test span/location in errors | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 186 |
| 227 | TODO | general | P3 | Test error suggestions | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 190 |
| 228 | TODO | general | P3 | Test import resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 206 |
| 229 | TODO | general | P3 | Test private symbol hiding | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 213 |
| 230 | TODO | general | P3 | Test circular import detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 217 |
| 231 | TODO | general | P3 | Test dependency graph resolution | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 224 |
| 232 | TODO | general | P3 | Test hot reload | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 228 |
| 233 | TODO | general | P3 | Test scope cleanup | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 244 |
| 234 | TODO | general | P3 | Test cache eviction | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 253 |
| 235 | TODO | general | P3 | Test refcount management | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 257 |
| 236 | TODO | general | P3 | Test leak detection | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 261 |
| 237 | TODO | general | P3 | Test deep recursion | `test/02_integration/compiler/compiler_interpreter_integration_spec.spl` | 265 |
| 238 | TODO | general | P3 | Create minimal MirModule and compile | `test/02_integration/compiler/llvm_backend_e2e_spec.spl` | 149 |
| 239 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 20 |
| 240 | TODO | general | P3 | Implement actual ELF reading | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 27 |
| 241 | TODO | general | P3 | Implement actual symbol parsing | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 33 |
| 242 | TODO | general | P3 | Implement actual size measurement | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 39 |
| 243 | TODO | general | P3 | Verify function order in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 118 |
| 244 | TODO | general | P3 | Verify actual ordering in binary | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 149 |
| 245 | TODO | general | P3 | Verify relocations are correct | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 270 |
| 246 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/02_integration/compiler/native_backend_e2e_spec.spl` | 346 |
| 247 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 68 |
| 248 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/interpreter/interpreter_bugs_spec.spl` | 108 |
| 249 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/03_system/compiler/parser_improvements_spec.spl` | 180 |
| 250 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 33 |
| 251 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 74 |
| 252 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 83 |
| 253 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 92 |
| 254 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 117 |
| 255 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/03_system/feature/usage/.spipe_matchers_set_literal_spec.spl` | 134 |
| 256 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/03_system/feature/usage/macro_validation_spec.spl` | 183 |
| 257 | TODO | general | P3 | Lambda default parameters not yet supported | `test/03_system/feature/usage/parser_default_keyword_spec.spl` | 146 |
| 258 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/03_system/feature/usage/primitive_types_spec.spl` | 61 |
| 259 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/03_system/feature/usage/set_literal_spec.spl` | 33 |
| 260 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/03_system/feature/usage/set_literal_spec.spl` | 74 |
| 261 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 83 |
| 262 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/03_system/feature/usage/set_literal_spec.spl` | 92 |
| 263 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 117 |
| 264 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/03_system/feature/usage/set_literal_spec.spl` | 134 |
| 265 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/03_system/feature/usage/trait_coherence_spec.spl` | 342 |
| 266 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1027 |
| 267 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1032 |
| 268 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1037 |
| 269 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/.spipe_matchers_database_sync_spec.spl` | 1042 |
| 270 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1051 |
| 271 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1056 |
| 272 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1061 |
| 273 | TODO | general | P3 | Implement async operations when Task type is available | `test/03_system/feature/app/database_sync_spec.spl` | 1066 |
| 274 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 68 |
| 275 | TODO | general | P3 | Implement conditional rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 72 |
| 276 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 83 |
| 277 | TODO | general | P3 | Implement list rendering | `test/03_system/feature/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 87 |
| 278 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 63 |
| 279 | TODO | general | P3 | Implement SSR | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 67 |
| 280 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 78 |
| 281 | TODO | general | P3 | Implement hydration | `test/03_system/feature/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 282 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 64 |
| 283 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 68 |
| 284 | TODO | general | P3 | Implement structural diff | `test/03_system/feature/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 72 |
| 285 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/03_system/generated/spec_matchers_spec.spl` | 63 |
| 286 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/05_perf/intensive/http/.spipe_matchers_h3_settings_write_frame_spec.spl` | 13 |
| 287 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/05_perf/intensive/http/h3_settings_write_frame_spec.spl` | 13 |
| 288 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 46 |
| 289 | TODO | general | P3 | Parse output from time -v or perf stat | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 60 |
| 290 | TODO | general | P3 | Compile source | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 69 |
| 291 | TODO | general | P3 | Use file stats | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 88 |
| 292 | TODO | general | P3 | Compile both versions | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 141 |
| 293 | TODO | general | P3 | Compile and measure | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 172 |
| 294 | TODO | general | P3 | Compile and measure | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 201 |
| 295 | TODO | general | P3 | Compile and measure | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 233 |
| 296 | TODO | general | P3 | Compile both and compare | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 267 |
| 297 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 341 |
| 298 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/.spipe_matchers_native_layout_performance_spec.spl` | 368 |
| 299 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/db/.spipe_wrapped_entry_db_ram_vs_persistent_bench_spec.spl` | 400 |
| 300 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/db/db_ram_vs_persistent_bench_spec.spl` | 340 |
| 301 | TODO | general | P3 | SMF loader currently cannot resolve time externs used in harness internals | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 164 |
| 302 | TODO | general | P3 | Enable once native compilation is confirmed stable in test runner. | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 172 |
| 303 | TODO | general | P3 | cross-module struct type metadata is not available in interpreter mode — | `test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl` | 176 |
| 304 | TODO | general | P3 | Execute binary and wait for completion | `test/05_perf/native_layout_performance_spec.spl` | 46 |
| 305 | TODO | general | P3 | Parse output from time -v or perf stat | `test/05_perf/native_layout_performance_spec.spl` | 60 |
| 306 | TODO | general | P3 | Compile source | `test/05_perf/native_layout_performance_spec.spl` | 69 |
| 307 | TODO | general | P3 | Use file stats | `test/05_perf/native_layout_performance_spec.spl` | 88 |
| 308 | TODO | general | P3 | Compile both versions | `test/05_perf/native_layout_performance_spec.spl` | 141 |
| 309 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 172 |
| 310 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 201 |
| 311 | TODO | general | P3 | Compile and measure | `test/05_perf/native_layout_performance_spec.spl` | 233 |
| 312 | TODO | general | P3 | Compile both and compare | `test/05_perf/native_layout_performance_spec.spl` | 267 |
| 313 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/05_perf/native_layout_performance_spec.spl` | 341 |
| 314 | TODO | general | P3 | Benchmark actual execution | `test/05_perf/native_layout_performance_spec.spl` | 368 |
| 315 | TODO | general | P3 | bench_run_warm + bench_emit require cross-module struct construction | `test/05_perf/web/web_server_bench_spec.spl` | 187 |
| 316 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 54 |
| 317 | TODO | general | P3 | Test function compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 61 |
| 318 | TODO | general | P3 | Test class compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 68 |
| 319 | TODO | general | P3 | Test struct compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 75 |
| 320 | TODO | general | P3 | Test enum compilation | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 79 |
| 321 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 95 |
| 322 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 102 |
| 323 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 109 |
| 324 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 113 |
| 325 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 117 |
| 326 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 133 |
| 327 | TODO | general | P3 | Test return type inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 137 |
| 328 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 141 |
| 329 | TODO | general | P3 | Test type error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 145 |
| 330 | TODO | general | P3 | Test recursive types | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 149 |
| 331 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 165 |
| 332 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 172 |
| 333 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 179 |
| 334 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 186 |
| 335 | TODO | general | P3 | Test error suggestions | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 190 |
| 336 | TODO | general | P3 | Test import resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 206 |
| 337 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 213 |
| 338 | TODO | general | P3 | Test circular import detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 217 |
| 339 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 224 |
| 340 | TODO | general | P3 | Test hot reload | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 228 |
| 341 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 244 |
| 342 | TODO | general | P3 | Test cache eviction | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 253 |
| 343 | TODO | general | P3 | Test refcount management | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 257 |
| 344 | TODO | general | P3 | Test leak detection | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 261 |
| 345 | TODO | general | P3 | Test deep recursion | `test/integration/compiler/compiler_interpreter_integration_spec.spl` | 265 |
| 346 | TODO | general | P3 | Create minimal MirModule and compile | `test/integration/compiler/llvm_backend_e2e_spec.spl` | 149 |
| 347 | TODO | general | P3 | Call compiler API to compile source_path -> output_path | `test/integration/compiler/native_backend_e2e_spec.spl` | 20 |
| 348 | TODO | general | P3 | Implement actual ELF reading | `test/integration/compiler/native_backend_e2e_spec.spl` | 26 |
| 349 | TODO | general | P3 | Implement actual symbol parsing | `test/integration/compiler/native_backend_e2e_spec.spl` | 32 |
| 350 | TODO | general | P3 | Implement actual size measurement | `test/integration/compiler/native_backend_e2e_spec.spl` | 38 |
| 351 | TODO | general | P3 | Verify function order in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 117 |
| 352 | TODO | general | P3 | Verify actual ordering in binary | `test/integration/compiler/native_backend_e2e_spec.spl` | 148 |
| 353 | TODO | general | P3 | Verify relocations are correct | `test/integration/compiler/native_backend_e2e_spec.spl` | 269 |
| 354 | TODO | general | P3 | Verify x86_64 machine type in ELF header | `test/integration/compiler/native_backend_e2e_spec.spl` | 345 |
| 355 | TODO | interpreter | P1 | Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. | `test/unit/lib/database/lib/nogc_sync_mut/io/signature_sffi.spl` | 129 |
| 356 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `test/unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 357 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `test/unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 358 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `test/unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 359 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `test/unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 360 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `test/unit/lib/database/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 361 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 362 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 363 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 364 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 365 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 366 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/unit/lib/database/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 367 | TODO | general | P3 | Integrate Simple interpreter here | `test/unit/lib/database/lib/gc_async_mut/gpu/browser_engine/script/simple_script.spl` | 62 |
| 368 | TODO | runtime | P2 | Interpreter loses the `self` binding when a struct | `test/unit/lib/database/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` | 1304 |
| 369 | TODO | quic-server | P2 | wire transport-level send queue | `test/unit/lib/database/lib/nogc_async_mut/io/quic/quic_server.spl` | 288 |
| 370 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `test/unit/lib/database/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 371 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/unit/lib/database/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 372 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/unit/lib/database/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 373 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 374 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 375 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 376 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/unit/lib/database/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 377 | TODO | stdlib | P2 | extract ALPN from handshake state when ALPN is implemented | `test/unit/lib/database/lib/nogc_async_mut/http_server/worker.spl` | 348 |
| 378 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `test/unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 379 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `test/unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 380 | TODO | general | P3 | lower to csrs in compiled mode | `test/unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 381 | TODO | general | P3 | lower to csrc in compiled mode | `test/unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 382 | TODO | general | P3 | lower to csrrw in compiled mode | `test/unit/lib/database/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 383 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `test/unit/lib/database/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 384 | TODO | general | P3 | support packed delta stream format | `test/unit/lib/database/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 385 | TODO | general | P3 | support packed delta stream format | `test/unit/lib/database/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 386 | TODO | general | P3 | Import bugdb handlers when available | `test/unit/app/desugar/app/mcp/bootstrap/main_optimized.spl` | 240 |
| 387 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `test/unit/app/desugar/app/itf/cmd_daily_debug.spl` | 159 |
| 388 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 42 |
| 389 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 47 |
| 390 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 54 |
| 391 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 59 |
| 392 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 66 |
| 393 | TODO | general | P3 | Implement after FileLock API is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 71 |
| 394 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 95 |
| 395 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 102 |
| 396 | TODO | general | P3 | Simulate write failure | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 107 |
| 397 | TODO | general | P3 | Implement after isolated DB path support | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 114 |
| 398 | TODO | general | P3 | Implement after process spawning is verified | `test/unit/app/tooling/test_db_concurrency_spec.spl` | 121 |
| 399 | TODO | general | P3 | Add memory profiling | `test/unit/app/tooling/test_db_performance_spec.spl` | 467 |
| 400 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/unit/app/tooling/test_db_integrity_spec.spl` | 427 |
| 401 | TODO | general | P3 | Enable tests once native codegen is complete | `test/unit/compiler/codegen/static_method_spec.spl` | 337 |
| 402 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `test/unit/compiler/compiler/80.driver/watcher/watcher_daemon.spl` | 70 |
| 403 | TODO | general | P3 | wire up hwprobe when available | `test/unit/compiler/compiler/30.types/simd_capabilities.spl` | 349 |
| 404 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `test/unit/compiler/compiler/driver/watcher/watcher_daemon.spl` | 70 |
| 405 | TODO | general | P3 | wire up hwprobe when available | `test/unit/compiler/compiler/types/simd_capabilities.spl` | 349 |
| 406 | TODO | general | P3 | walrus operator `:=` triggers parse error (expected indented block after ':') | `test/unit/compiler/frontend/parser_spec.spl` | 30 |
| 407 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_eval_spec.spl` | 10 |
| 408 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_lower_spec.spl` | 10 |
| 409 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_module_spec.spl` | 10 |
| 410 | TODO | general | P3 | Enable when hir module is ready for import | `test/unit/compiler/hir/hir_types_spec.spl` | 10 |
| 411 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/unit/compiler/loader/jit_context_spec.spl` | 209 |
| 412 | TODO | general | P3 | Add TypeRegistry validation | `test/unit/compiler/loader/jit_context_spec.spl` | 336 |
| 413 | TODO | general | P3 | Create test template and type args | `test/unit/compiler/loader/jit_context_spec.spl` | 388 |
| 414 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/unit/compiler/loader/jit_context_spec.spl` | 397 |
| 415 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/unit/compiler/loader/jit_context_spec.spl` | 401 |
| 416 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 405 |
| 417 | TODO | general | P3 | Verify DI container passed to compilation | `test/unit/compiler/loader/jit_context_spec.spl` | 409 |
| 418 | TODO | interpreter | P1 | Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. | `test/unit/compiler/std/nogc_sync_mut/io/signature_sffi.spl` | 129 |
| 419 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `test/unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 420 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `test/unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 421 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `test/unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 422 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `test/unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 423 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `test/unit/compiler/std/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 424 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/unit/compiler/std/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 425 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/unit/compiler/std/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 426 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 427 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 428 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 429 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/unit/compiler/std/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 430 | TODO | general | P3 | Integrate Simple interpreter here | `test/unit/compiler/std/gc_async_mut/gpu/browser_engine/script/simple_script.spl` | 62 |
| 431 | TODO | runtime | P2 | Interpreter loses the `self` binding when a struct | `test/unit/compiler/std/gc_async_mut/gpu/engine2d/backend_metal.spl` | 1304 |
| 432 | TODO | quic-server | P2 | wire transport-level send queue | `test/unit/compiler/std/nogc_async_mut/io/quic/quic_server.spl` | 288 |
| 433 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `test/unit/compiler/std/nogc_async_mut/gpu/memory.spl` | 244 |
| 434 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/unit/compiler/std/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 435 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/unit/compiler/std/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 436 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 437 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 438 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 439 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/unit/compiler/std/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 440 | TODO | stdlib | P2 | extract ALPN from handshake state when ALPN is implemented | `test/unit/compiler/std/nogc_async_mut/http_server/worker.spl` | 348 |
| 441 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `test/unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 442 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `test/unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 443 | TODO | general | P3 | lower to csrs in compiled mode | `test/unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 444 | TODO | general | P3 | lower to csrc in compiled mode | `test/unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 445 | TODO | general | P3 | lower to csrrw in compiled mode | `test/unit/compiler/std/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 446 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `test/unit/compiler/std/skia/bridge/engine2d_bridge.spl` | 125 |
| 447 | TODO | general | P3 | support packed delta stream format | `test/unit/compiler/std/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 448 | TODO | general | P3 | support packed delta stream format | `test/unit/compiler/std/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 449 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 246 |
| 450 | TODO | general | P3 | full context validation needs MachInst infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 258 |
| 451 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 270 |
| 452 | TODO | general | P3 | full contract validation needs backend_types/riscv_target infrastructure | `test/unit/rtl/encode_riscv_spec.spl` | 282 |
| 453 | TODO | general | P3 | implement a non-destructive signature probe when the runtime supports it | `test/unit/sffi/sffi_public_api_spec.spl` | 112 |
| 454 | TODO | general | P3 | Move back to unit spec once compiled-mode test execution lands. | `test/perf/intensive/http/h3_settings_write_frame_spec.spl` | 13 |
| 455 | TODO | general | P3 | Execute binary and wait for completion | `test/perf/native_layout_performance_spec.spl` | 46 |
| 456 | TODO | general | P3 | Parse output from time -v or perf stat | `test/perf/native_layout_performance_spec.spl` | 60 |
| 457 | TODO | general | P3 | Compile source | `test/perf/native_layout_performance_spec.spl` | 69 |
| 458 | TODO | general | P3 | Use file stats | `test/perf/native_layout_performance_spec.spl` | 88 |
| 459 | TODO | general | P3 | Compile both versions | `test/perf/native_layout_performance_spec.spl` | 141 |
| 460 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 172 |
| 461 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 201 |
| 462 | TODO | general | P3 | Compile and measure | `test/perf/native_layout_performance_spec.spl` | 233 |
| 463 | TODO | general | P3 | Compile both and compare | `test/perf/native_layout_performance_spec.spl` | 267 |
| 464 | TODO | general | P3 | Benchmark compiling the Simple compiler itself | `test/perf/native_layout_performance_spec.spl` | 341 |
| 465 | TODO | general | P3 | Benchmark actual execution | `test/perf/native_layout_performance_spec.spl` | 368 |
| 466 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/compiler/parser_improvements_spec.spl` | 170 |
| 467 | TODO | general | P3 | Implement conditional rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 68 |
| 468 | TODO | general | P3 | Implement conditional rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 72 |
| 469 | TODO | general | P3 | Implement list rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 83 |
| 470 | TODO | general | P3 | Implement list rendering | `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl` | 87 |
| 471 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 63 |
| 472 | TODO | general | P3 | Implement SSR | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 67 |
| 473 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 78 |
| 474 | TODO | general | P3 | Implement hydration | `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl` | 82 |
| 475 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 64 |
| 476 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 68 |
| 477 | TODO | general | P3 | Implement structural diff | `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl` | 72 |
| 478 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/system/generated/spec_matchers_spec.spl` | 63 |
| 479 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 68 |
| 480 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/system/interpreter/interpreter_bugs_spec.spl` | 108 |
| 481 | TODO | general | P3 | Import bugdb handlers when available | `test/feature/lib/app/mcp/bootstrap/main_optimized.spl` | 240 |
| 482 | TODO | general | P3 | use a real calendar formatter; unix-seconds bucket suffices for | `test/feature/lib/app/itf/cmd_daily_debug.spl` | 159 |
| 483 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `test/feature/lib/compiler/80.driver/watcher/watcher_daemon.spl` | 70 |
| 484 | TODO | general | P3 | wire up hwprobe when available | `test/feature/lib/compiler/30.types/simd_capabilities.spl` | 349 |
| 485 | TODO | general | P3 | original phantom API filtered excludes (target/, .git/, *.swp, *.tmp); | `test/feature/lib/compiler/driver/watcher/watcher_daemon.spl` | 70 |
| 486 | TODO | general | P3 | wire up hwprobe when available | `test/feature/lib/compiler/types/simd_capabilities.spl` | 349 |
| 487 | TODO | interpreter | P1 | Simple wraps SFFI [u8] returns as Option::Some([bytes]) at the call-site binding even when the wrapper return type says plain [u8] and unwraps internally. Repro: 17 failing tests in test/03_system/os_crypto_ref_signature_spec.spl with "method len not found on type enum (receiver value: Option::Some(...))". Root cause likely in src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs return marshalling or in the type checker's handling of multi-decl externs (see fs.spl vs ffi/io.spl conflict for rt_file_read_bytes pattern). Wrapper-side `_unwrap_sig` doesn't propagate. Full notes in doc/09_report/crypto_spec_remains_2026-04-16.md. | `test/feature/lib/lib/nogc_sync_mut/io/signature_sffi.spl` | 129 |
| 488 | TODO | general | P3 | Phase 5 — rt_cuda_malloc + rt_cuda_memcpy_h2d for body arrays | `test/feature/lib/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 57 |
| 489 | TODO | general | P3 | Phase 5 — upload constraint SoA to device | `test/feature/lib/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 61 |
| 490 | TODO | general | P3 | Phase 5 — for each color: launch kernel(batch_offset, batch_count) | `test/feature/lib/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 65 |
| 491 | TODO | general | P3 | Phase 5 — position correction kernel per color batch | `test/feature/lib/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 73 |
| 492 | TODO | general | P3 | Phase 5 — rt_cuda_memcpy_d2h velocity/position arrays back | `test/feature/lib/lib/nogc_sync_mut/engine/physics/backend_gpu/gpu_solver.spl` | 79 |
| 493 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/feature/lib/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 494 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/feature/lib/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 495 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/feature/lib/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 496 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/feature/lib/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 497 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/feature/lib/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 498 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/feature/lib/lib/nogc_sync_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 499 | TODO | general | P3 | Integrate Simple interpreter here | `test/feature/lib/lib/gc_async_mut/gpu/browser_engine/script/simple_script.spl` | 62 |
| 500 | TODO | runtime | P2 | Interpreter loses the `self` binding when a struct | `test/feature/lib/lib/gc_async_mut/gpu/engine2d/backend_metal.spl` | 1304 |
| 501 | TODO | quic-server | P2 | wire transport-level send queue | `test/feature/lib/lib/nogc_async_mut/io/quic/quic_server.spl` | 288 |
| 502 | TODO | general | P3 | add typed upload variants (upload_f64, upload_i32, etc.) | `test/feature/lib/lib/nogc_async_mut/gpu/memory.spl` | 244 |
| 503 | TODO | general | P3 | replace placeholder zeroed serialization with real f32→[u8] packing | `test/feature/lib/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 297 |
| 504 | TODO | general | P3 | real f32/i64 serialization — zeroed placeholder for now | `test/feature/lib/lib/nogc_async_mut/engine/render/gpu_lighting3d.spl` | 305 |
| 505 | TODO | general | P3 | replace placeholder zeroed byte buffers with real float serialization | `test/feature/lib/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 93 |
| 506 | TODO | general | P3 | real float serialization — build zeroed placeholder bytes for now | `test/feature/lib/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 104 |
| 507 | TODO | general | P3 | upload real f64→[u8] per-instance transform data once rt_f64_to_bytes | `test/feature/lib/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 161 |
| 508 | TODO | general | P3 | serialize InstanceData fields into real bytes once rt_f64_to_bytes lands | `test/feature/lib/lib/nogc_async_mut/engine/render/gpu_mesh3d.spl` | 177 |
| 509 | TODO | stdlib | P2 | extract ALPN from handshake state when ALPN is implemented | `test/feature/lib/lib/nogc_async_mut/http_server/worker.spl` | 348 |
| 510 | TODO | general | P3 | when targeting baremetal, lower to real csrr via asm switch | `test/feature/lib/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 165 |
| 511 | TODO | general | P3 | when targeting baremetal, lower to real csrw via asm switch | `test/feature/lib/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 181 |
| 512 | TODO | general | P3 | lower to csrs in compiled mode | `test/feature/lib/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 194 |
| 513 | TODO | general | P3 | lower to csrc in compiled mode | `test/feature/lib/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 207 |
| 514 | TODO | general | P3 | lower to csrrw in compiled mode | `test/feature/lib/lib/nogc_async_mut_noalloc/baremetal/riscv/csr.spl` | 217 |
| 515 | TODO | general | P3 | map DrawRRect / DrawPath / DrawTextBlob / DrawLine(stroke) / | `test/feature/lib/lib/skia/bridge/engine2d_bridge.spl` | 125 |
| 516 | TODO | general | P3 | support packed delta stream format | `test/feature/lib/lib/skia/feature/glyph/ot_parser_gvar.spl` | 111 |
| 517 | TODO | general | P3 | support packed delta stream format | `test/feature/lib/lib/skia/feature/glyph/ot_parser_gvar.spl` | 231 |
| 518 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/feature/usage/macro_validation_spec.spl` | 183 |
| 519 | TODO | general | P3 | Lambda default parameters not yet supported | `test/feature/usage/parser_default_keyword_spec.spl` | 146 |
| 520 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/feature/usage/primitive_types_spec.spl` | 61 |
| 521 | TODO | general | P3 | set type and set operations not yet implemented — using array placeholders | `test/feature/usage/set_literal_spec.spl` | 33 |
| 522 | TODO | general | P3 | s{} union operator not yet implemented — using array concat | `test/feature/usage/set_literal_spec.spl` | 74 |
| 523 | TODO | general | P3 | s{} intersect operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 83 |
| 524 | TODO | general | P3 | s{} diff operator not yet implemented — using filter | `test/feature/usage/set_literal_spec.spl` | 92 |
| 525 | TODO | general | P3 | s{} is_subset operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 117 |
| 526 | TODO | general | P3 | s{} is_disjoint operator not yet implemented — using manual check | `test/feature/usage/set_literal_spec.spl` | 134 |
| 527 | TODO | general | P3 | Enable when decorator on impl blocks is supported | `test/feature/usage/trait_coherence_spec.spl` | 342 |
