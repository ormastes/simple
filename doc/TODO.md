# TODO Tracking

**Total:** 331 items | **Open:** 331 | **Blocked:** 0

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 0 |
| P1 | 0 |
| P2 | 0 |
| P3 | 331 |

## By Area

| Area | Count |
|------|-------|
| general | 331 |

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | When SMF loader is available in Simple, load and execute directly | `src/app/cli/main.spl` | 394 |
| 1 | TODO | general | P3 | Import and use parallel.spl and incremental.spl | `src/app/duplicate_check/detector.spl` | 438 |
| 2 | TODO | general | P3 | Parallel processing implementation | `src/app/duplicate_check/parallel.spl` | 42 |
| 3 | TODO | general | P3 | Traverse children based on type_id | `src/app/gc/core.spl` | 284 |
| 4 | TODO | general | P3 | Use FFI to read memory | `src/app/gc/core.spl` | 396 |
| 5 | TODO | general | P3 | Use FFI to write memory | `src/app/gc/core.spl` | 401 |
| 6 | TODO | general | P3 | Use FFI to read memory | `src/app/gc/core.spl` | 406 |
| 7 | TODO | general | P3 | Use FFI to write memory | `src/app/gc/core.spl` | 411 |
| 8 | TODO | general | P3 | Store logger callback in GCCore | `src/app/gc/core.spl` | 448 |
| 9 | TODO | general | P3 | send DOWN message | `src/app/interpreter/async_runtime/actor_scheduler.spl` | 543 |
| 10 | TODO | general | P3 | Remove these once static method calls are supported in interpreter | `src/app/interpreter/collections/persistent_dict.spl` | 35 |
| 11 | TODO | general | P3 | Re-enable when collections module is complete | `src/app/interpreter/core/environment.spl` | 12 |
| 12 | TODO | general | P3 | Re-enable when complete | `src/app/interpreter/core/eval.spl` | 10 |
| 13 | TODO | general | P3 | Re-enable when Lazy and PersistentDict are complete | `src/app/interpreter/core/eval.spl` | 20 |
| 14 | TODO | general | P3 | Re-enable when Lazy and PersistentDict are complete | `src/app/interpreter/core/eval.spl` | 39 |
| 15 | TODO | general | P3 | Get actual source location from function definition | `src/app/interpreter/expr/calls.spl` | 90 |
| 16 | TODO | general | P3 | Re-enable when RuntimeValue.Tensor variant is added | `src/app/interpreter/expr/__init__.spl` | 269 |
| 17 | TODO | general | P3 | Re-enable when AST construction syntax is fixed | `src/app/interpreter/helpers/macros.spl` | 251 |
| 18 | TODO | general | P3 | Re-enable platform-specific command resolution when using full parser | `src/app/io/mod.spl` | 499 |
| 19 | TODO | general | P3 | Implement Windows timeout using PowerShell or .NET | `src/app/io/mod.spl` | 518 |
| 20 | TODO | general | P3 | Implement memory_bytes, cpu_seconds, max_fds, max_procs limits | `src/app/io/mod.spl` | 537 |
| 21 | TODO | general | P3 | When compiler modules can run in interpreter mode, use pure-Simple LLVM path: | `src/app/io/mod.spl` | 1103 |
| 22 | TODO | general | P3 | Import and use BaremetalBuilder directly once module imports work | `src/app/io/mod.spl` | 1127 |
| 23 | TODO | general | P3 | Import and use compiler.driver and compiler.backend.llvm_backend | `src/app/io/mod.spl` | 1161 |
| 24 | TODO | general | P3 | Implement Lean 4 verification integration | `src/app/lsp/handlers/verification.spl` | 35 |
| 25 | TODO | general | P3 | Use proper SPK format once FFI is ready | `src/app/package/build.spl` | 103 |
| 26 | TODO | general | P3 | Verify checksum when FFI is available | `src/app/package/verify.spl` | 67 |
| 27 | TODO | general | P3 | Implement serial port reading | `src/app/semihost/reader.spl` | 176 |
| 28 | TODO | general | P3 | Implement OpenOCD GDB RSP connection | `src/app/semihost/reader.spl` | 207 |
| 29 | TODO | general | P3 | Implement proper SMF parsing | `src/app/semihost/reader.spl` | 382 |
| 30 | TODO | general | P3 | Implement proper stdin reading | `src/app/semihost/reader.spl` | 404 |
| 31 | TODO | general | P3 | Use actual time | `src/app/semihost/reader.spl` | 410 |
| 32 | TODO | general | P3 | Implement proper ANSI stripping when rt_char_code FFI is available | `src/app/test_runner_new/test_runner_files.spl` | 17 |
| 33 | TODO | general | P3 | When rt_process_spawn_async is available, run truly in parallel | `src/app/test_runner_new/test_runner_parallel.spl` | 52 |
| 34 | TODO | general | P3 | Submit PR to index repo to set yanked=false | `src/app/yank/main.spl` | 79 |
| 35 | TODO | general | P3 | Submit PR to index repo to set yanked=true | `src/app/yank/main.spl` | 87 |
| 36 | TODO | general | P3 | Use filesystem FFI | `src/compiler/backend/exhaustiveness_validator.spl` | 208 |
| 37 | TODO | general | P3 | Capture free variables | `src/compiler/backend/interpreter.spl` | 217 |
| 38 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 685 |
| 39 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 698 |
| 40 | TODO | general | P3 | Convert ptr to Simple string | `src/compiler/backend/interpreter.spl` | 704 |
| 41 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 715 |
| 42 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 727 |
| 43 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 740 |
| 44 | TODO | general | P3 | Convert ptr to Simple string | `src/compiler/backend/interpreter.spl` | 745 |
| 45 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 756 |
| 46 | TODO | general | P3 | Proper string conversion (ptr + len) | `src/compiler/backend/interpreter.spl` | 780 |
| 47 | TODO | general | P3 | Implement full conversion for Array, Dict, etc. | `src/compiler/backend/interpreter.spl` | 784 |
| 48 | TODO | general | P3 | Implement full type conversion for all Simple types | `src/compiler/backend/jit_interpreter.spl` | 228 |
| 49 | TODO | general | P3 | Pass floats as i64 bit pattern | `src/compiler/backend/jit_interpreter.spl` | 235 |
| 50 | TODO | general | P3 | Determine actual return type from function signature | `src/compiler/backend/jit_interpreter.spl` | 248 |
| 51 | TODO | general | P3 | Fix parse errors in backend/*.spl (runtime parser bugs) | `src/compiler/backend.spl` | 23 |
| 52 | TODO | general | P3 | Backends commented out due to parse errors | `src/compiler/backend.spl` | 36 |
| 53 | TODO | general | P3 | Backends commented out due to parse errors | `src/compiler/backend.spl` | 41 |
| 54 | TODO | general | P3 | Backend implementations commented out due to parse errors | `src/compiler/backend.spl` | 55 |
| 55 | TODO | general | P3 | Load expr into reg | `src/compiler/backend/x86_asm.spl` | 111 |
| 56 | TODO | general | P3 | Store reg into var | `src/compiler/backend/x86_asm.spl` | 116 |
| 57 | TODO | general | P3 | Use rt_cli_get_args() | `src/compiler/baremetal/link_wrapper.spl` | 291 |
| 58 | TODO | general | P3 | Use rt_exit() | `src/compiler/baremetal/link_wrapper.spl` | 295 |
| 59 | TODO | general | P3 | Implement via FFI | `src/compiler/build_native.spl` | 312 |
| 60 | TODO | general | P3 | Extract code before first await from func_body | `src/compiler/desugar/poll_generator.spl` | 156 |
| 61 | TODO | general | P3 | Extract return value from func_body | `src/compiler/desugar/poll_generator.spl` | 179 |
| 62 | TODO | general | P3 | Apply final computation from function body | `src/compiler/desugar/poll_generator.spl` | 319 |
| 63 | TODO | general | P3 | Report detailed errors when diagnostics system supports them | `src/compiler/hir_lowering/async.spl` | 183 |
| 64 | TODO | general | P3 | Parse and interpret | `src/compiler/init.spl` | 140 |
| 65 | TODO | general | P3 | Load and interpret file | `src/compiler/init.spl` | 144 |
| 66 | TODO | general | P3 | JIT compile and execute | `src/compiler/init.spl` | 159 |
| 67 | TODO | general | P3 | JIT compile and execute file | `src/compiler/init.spl` | 163 |
| 68 | TODO | general | P3 | Compile to native code | `src/compiler/init.spl` | 167 |
| 69 | TODO | general | P3 | Compile to object file | `src/compiler/init.spl` | 184 |
| 70 | TODO | general | P3 | Implement actual parsing | `src/compiler/init.spl` | 263 |
| 71 | TODO | general | P3 | Load actual templates from input SMF TemplateCode sections | `src/compiler/linker/lazy_instantiator.spl` | 183 |
| 72 | TODO | general | P3 | Implement proper relocation parsing to find references | `src/compiler/linker/link.spl` | 292 |
| 73 | TODO | general | P3 | Implement proper SMF writing | `src/compiler/linker/link.spl` | 422 |
| 74 | TODO | general | P3 | Load runtime symbols | `src/compiler/linker/mold.spl` | 287 |
| 75 | TODO | general | P3 | Implement SMF to object compilation | `src/compiler/linker/object_resolver.spl` | 133 |
| 76 | TODO | general | P3 | Implement proper template parsing | `src/compiler/linker/obj_taker.spl` | 561 |
| 77 | TODO | general | P3 | Implement directory scanning | `src/compiler/linker/smf_getter.spl` | 168 |
| 78 | TODO | general | P3 | Create SmfReaderImpl from in-memory data | `src/compiler/linker/smf_getter.spl` | 248 |
| 79 | TODO | general | P3 | Implement proper template parsing | `src/compiler/linker/smf_reader.spl` | 239 |
| 80 | TODO | general | P3 | Implement section table reading | `src/compiler/linker/smf_reader.spl` | 266 |
| 81 | TODO | general | P3 | Implement proper byte-to-char conversion | `src/compiler/linker/smf_reader.spl` | 354 |
| 82 | TODO | general | P3 | Real code generation | `src/compiler/loader/compiler_ffi.spl` | 162 |
| 83 | TODO | general | P3 | Real type checking | `src/compiler/loader/compiler_ffi.spl` | 202 |
| 84 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 403 |
| 85 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 421 |
| 86 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 446 |
| 87 | TODO | general | P3 | Re-enable when mmap functions are available in app.io.mod | `src/compiler/loader/jit_instantiator.spl` | 10 |
| 88 | TODO | general | P3 | Add these functions to app.io.mod when implementing executable memory support | `src/compiler/loader/jit_instantiator.spl` | 12 |
| 89 | TODO | general | P3 | Load actual template bytes from SMF TemplateCode section | `src/compiler/loader/jit_instantiator.spl` | 360 |
| 90 | TODO | general | P3 | Compile via FFI (stub for now - actual implementation needs JSON serialization) | `src/compiler/loader/jit_instantiator.spl` | 372 |
| 91 | TODO | general | P3 | Implement proper SMF update | `src/compiler/loader/jit_instantiator.spl` | 427 |
| 92 | TODO | general | P3 | Add mmap functions to app.io.mod when implementing memory-mapped file support | `src/compiler/loader/smf_cache.spl` | 21 |
| 93 | TODO | general | P3 | Parse section table for accurate offsets | `src/compiler/loader/smf_cache.spl` | 82 |
| 94 | TODO | general | P3 | Parse section table and read section | `src/compiler/loader/smf_cache.spl` | 153 |
| 95 | TODO | general | P3 | Implement proper type checking | `src/compiler/mir_bitfield.spl` | 17 |
| 96 | TODO | general | P3 | Look up bitfield in symbol table | `src/compiler/mir_bitfield.spl` | 24 |
| 97 | TODO | general | P3 | Proper iterator lowering | `src/compiler/mir_lowering.spl` | 562 |
| 98 | TODO | general | P3 | Create copy instructions for argument binding | `src/compiler/mir_opt/inline.spl` | 222 |
| 99 | TODO | general | P3 | Replace return with assignment to call_dest | `src/compiler/mir_opt/inline.spl` | 230 |
| 100 | TODO | general | P3 | Implement proper local renaming | `src/compiler/mir_opt/inline.spl` | 253 |
| 101 | TODO | general | P3 | Implement actual inlining logic | `src/compiler/mir_opt/inline.spl` | 359 |
| 102 | TODO | general | P3 | Implement full module-level inlining | `src/compiler/mir_opt/inline.spl` | 409 |
| 103 | TODO | general | P3 | Implement iteration count analysis | `src/compiler/mir_opt/loop_opt.spl` | 91 |
| 104 | TODO | general | P3 | Implement full LICM algorithm | `src/compiler/mir_opt/loop_opt.spl` | 291 |
| 105 | TODO | general | P3 | Implement loop unrolling | `src/compiler/mir_opt/loop_opt.spl` | 349 |
| 106 | TODO | general | P3 | Implement strength reduction patterns | `src/compiler/mir_opt/loop_opt.spl` | 428 |
| 107 | TODO | general | P3 |  | `src/compiler/module_resolver/manifest.spl` | 442 |
| 108 | TODO | general | P3 | These should be proper FFI functions | `src/compiler/module_resolver/resolution.spl` | 302 |
| 109 | TODO | general | P3 | Proper FFI function | `src/compiler/module_resolver/resolution.spl` | 324 |
| 110 | TODO | general | P3 |  | `src/compiler/module_resolver/resolution.spl` | 460 |
| 111 | TODO | general | P3 | These should be proper FFI functions | `src/compiler/module_resolver/types.spl` | 431 |
| 112 | TODO | general | P3 | Proper FFI function | `src/compiler/module_resolver/types.spl` | 449 |
| 113 | TODO | general | P3 |  | `src/compiler/module_resolver/types.spl` | 511 |
| 114 | TODO | general | P3 | Use file I/O FFI when available | `src/compiler/monomorphize/deferred.spl` | 178 |
| 115 | TODO | general | P3 | Implement proper SMF parsing with loader | `src/compiler/monomorphize/deferred.spl` | 182 |
| 116 | TODO | general | P3 | Create minimal FunctionDef | `src/compiler/monomorphize/deferred.spl` | 286 |
| 117 | TODO | general | P3 | Use Monomorphizer.specialize_function when available | `src/compiler/monomorphize/deferred.spl` | 341 |
| 118 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 372 |
| 119 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 398 |
| 120 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 424 |
| 121 | TODO | general | P3 | Proper calculation using section table | `src/compiler/monomorphize/hot_reload.spl` | 302 |
| 122 | TODO | general | P3 | Implement file_write_at FFI for offset writes | `src/compiler/monomorphize/hot_reload.spl` | 352 |
| 123 | TODO | general | P3 | Implement file_read_at FFI for offset reads | `src/compiler/monomorphize/hot_reload.spl` | 363 |
| 124 | TODO | general | P3 |  | `src/compiler/monomorphize/hot_reload.spl` | 568 |
| 125 | TODO | general | P3 |  | `src/compiler/monomorphize/metadata.spl` | 413 |
| 126 | TODO | general | P3 | Convert AST type to ConcreteType | `src/compiler/monomorphize/partition.spl` | 203 |
| 127 | TODO | general | P3 | Convert AST type to ConcreteType | `src/compiler/monomorphize/partition.spl` | 210 |
| 128 | TODO | general | P3 |  | `src/compiler/monomorphize/partition.spl` | 615 |
| 129 | TODO | general | P3 |  | `src/compiler/monomorphize/tracker.spl` | 506 |
| 130 | TODO | general | P3 | Full union support (would need ConcreteType.Union variant) | `src/compiler/monomorphize/util.spl` | 241 |
| 131 | TODO | general | P3 |  | `src/compiler/monomorphize/util.spl` | 502 |
| 132 | TODO | general | P3 | Parse interpolations | `src/compiler/parser.spl` | 1217 |
| 133 | TODO | general | P3 | Implement proper parsing | `src/compiler/parser.spl` | 2295 |
| 134 | TODO | general | P3 | Implement proper parsing | `src/compiler/parser_types.spl` | 734 |
| 135 | TODO | general | P3 | val hir = lower_to_hir(specialized) | `src/compiler/pipeline_fn.spl` | 52 |
| 136 | TODO | general | P3 | var mir = lower_to_mir(hir, contract_mode, di) | `src/compiler/pipeline_fn.spl` | 56 |
| 137 | TODO | general | P3 | val code = codegen_to_native(mir) | `src/compiler/pipeline_fn.spl` | 67 |
| 138 | TODO | general | P3 | Full expression type inference requires type checker integration | `src/compiler/query_api.spl` | 280 |
| 139 | TODO | general | P3 | Implement enhanced trait method resolution | `src/compiler/resolve.spl` | 695 |
| 140 | TODO | general | P3 | Implement actual AST serialization (Phase 3) | `src/compiler/smf_writer.spl` | 354 |
| 141 | TODO | general | P3 | Implement full metadata serialization (Phase 3) | `src/compiler/smf_writer.spl` | 398 |
| 142 | TODO | general | P3 | Proper ELF/object parsing | `src/compiler/smf_writer.spl` | 479 |
| 143 | TODO | general | P3 | Lower type_args when available | `src/compiler/type_infer/inference.spl` | 366 |
| 144 | TODO | general | P3 | Re-enable when using full parser that supports 'mod package.submodule' syntax | `src/compiler/type_infer.spl` | 113 |
| 145 | TODO | general | P3 | Properly map type parameters to type arguments | `src/compiler/type_infer/traits.spl` | 185 |
| 146 | TODO | general | P3 | Properly map bound.type_param to the corresponding type_arg | `src/compiler/type_infer/traits.spl` | 196 |
| 147 | TODO | general | P3 | Determine which trait defines this method | `src/compiler/type_infer/traits.spl` | 210 |
| 148 | TODO | general | P3 | Check pattern, bind variables | `src/compiler/type_system/bidirectional.spl` | 165 |
| 149 | TODO | general | P3 | Implement bidirectional variants for let bindings, etc. | `src/compiler/type_system/bidirectional.spl` | 395 |
| 150 | TODO | general | P3 | Get FString keys and validate dict argument | `src/compiler/type_system/expr_infer.spl` | 689 |
| 151 | TODO | general | P3 | Check pattern against subject type | `src/compiler/type_system/stmt_check.spl` | 361 |
| 152 | TODO | general | P3 | Bind pattern variables | `src/compiler/type_system/stmt_check.spl` | 362 |
| 153 | TODO | general | P3 | Implement calc step checking | `src/compiler/type_system/stmt_check.spl` | 514 |
| 154 | TODO | general | P3 | Check classes, structs, enums, traits, impls | `src/compiler/visibility_integration.spl` | 26 |
| 155 | TODO | general | P3 | Re-enable when parser supports mutable field updates | `src/lib/database/feature.spl` | 264 |
| 156 | TODO | general | P3 | Implement proper wait logic | `src/lib/execution/mod.spl` | 173 |
| 157 | TODO | general | P3 | Implement proper event handling | `src/lib/execution/mod.spl` | 204 |
| 158 | TODO | general | P3 | Print to stdout (Phase 3.4 - needs SFFI support for stdout) | `src/lib/hooks/stop.spl` | 154 |
| 159 | TODO | general | P3 | Read line from stdin (Phase 3.4 - needs SFFI support for stdin) | `src/lib/hooks/stop.spl` | 160 |
| 160 | TODO | general | P3 | Remove once interpreter supports static methods | `src/lib/pure/autograd.spl` | 92 |
| 161 | TODO | general | P3 | Zero gradients when autograd is available | `src/lib/pure/nn.spl` | 291 |
| 162 | TODO | general | P3 | Merge back to generic PureTensor<T> once interpreter supports generics | `src/lib/pure/tensor_f64.spl` | 4 |
| 163 | TODO | general | P3 | Remove this file once interpreter supports: | `src/lib/pure/tensor_factory.spl` | 6 |
| 164 | TODO | general | P3 | Remove these once interpreter supports static methods on generic types | `src/lib/pure/tensor.spl` | 96 |
| 165 | TODO | general | P3 | Integration point - When debugger FFI is available: | `src/runtime/hooks.spl` | 493 |
| 166 | TODO | general | P3 | Implement request-response pattern | `src/std/actors/actor.spl` | 73 |
| 167 | TODO | general | P3 | Back-pressure handling | `src/std/actors/actor.spl` | 99 |
| 168 | TODO | general | P3 | Invoke method on actor_instance | `src/std/actors/actor.spl` | 182 |
| 169 | TODO | general | P3 | Call cleanup hooks | `src/std/actors/actor.spl` | 214 |
| 170 | TODO | general | P3 | Integrate with timer | `src/std/async_host/combinators.spl` | 44 |
| 171 | TODO | general | P3 | Add compile-time runtime selection when conditional compilation is implemented | `src/std/async_unified.spl` | 16 |
| 172 | TODO | general | P3 | Implement generational collection | `src/std/gc.spl` | 356 |
| 173 | TODO | general | P3 | Use type information to find pointers | `src/std/gc.spl` | 429 |
| 174 | TODO | general | P3 | Call type-specific finalizer | `src/std/gc.spl` | 530 |
| 175 | TODO | general | P3 | gpu_vulkan(device) | `src/std/gpu/context.spl` | 81 |
| 176 | TODO | general | P3 | Return error or dummy stream | `src/std/gpu/context.spl` | 175 |
| 177 | TODO | general | P3 | Add cuda device sync | `src/std/gpu/device.spl` | 35 |
| 178 | TODO | general | P3 | Add vulkan device sync | `src/std/gpu/device.spl` | 38 |
| 179 | TODO | general | P3 | Use proper sizeof[T]() when available | `src/std/gpu/memory.spl` | 34 |
| 180 | TODO | general | P3 | Implement upload via tensor operations | `src/std/gpu/memory.spl` | 49 |
| 181 | TODO | general | P3 | Implement download via tensor operations | `src/std/gpu/memory.spl` | 63 |
| 182 | TODO | general | P3 | Implement via tensor copy | `src/std/gpu/memory.spl` | 82 |
| 183 | TODO | general | P3 | Create tensor on GPU device | `src/std/gpu/memory.spl` | 114 |
| 184 | FIXME | general | P3 | Should return Some(Arc(self.ptr)) but can't construct Arc/Rc | `src/std/rc.spl` | 260 |
| 185 | TODO | general | P3 | Re-enable generic version after bootstrap generics support | `src/std/src/di.spl` | 174 |
| 186 | TODO | general | P3 | Execute HIR via instruction module | `src/std/src/di.spl` | 344 |
| 187 | TODO | general | P3 | Implement via FFI to Rust codegen | `src/std/src/di.spl` | 363 |
| 188 | TODO | general | P3 | Implement via FFI | `src/std/src/di.spl` | 465 |
| 189 | TODO | general | P3 | Implement via FFI | `src/std/src/di.spl` | 481 |
| 190 | TODO | general | P3 | Re-enable generic version after bootstrap generics support | `src/std/src/di.spl` | 647 |
| 191 | TODO | general | P3 | Use proper FFI when available | `src/std/src/exp/config.spl` | 438 |
| 192 | TODO | general | P3 | Wire to Rust FFI check | `src/std/src/math/backend.spl` | 115 |
| 193 | TODO | general | P3 | Wire to Rust FFI check | `src/std/src/math/backend.spl` | 120 |
| 194 | TODO | general | P3 | Native backend implementation | `src/std/src/tensor/factory.spl` | 236 |
| 195 | TODO | general | P3 | Return actual dtype from handle | `src/std/src/tensor.spl` | 111 |
| 196 | TODO | general | P3 | This assumes we have file write via fs or similar | `test/app/package/ffi_spec.spl` | 17 |
| 197 | TODO | general | P3 | Test interrupt enable | `test/baremetal/arm32_boot_spec.spl` | 81 |
| 198 | TODO | general | P3 | Test priority levels | `test/baremetal/arm32_boot_spec.spl` | 87 |
| 199 | TODO | general | P3 | Test SysTick | `test/baremetal/arm32_boot_spec.spl` | 103 |
| 200 | TODO | general | P3 | Test exception handling | `test/baremetal/arm64_boot_spec.spl` | 59 |
| 201 | TODO | general | P3 | String iteration (for now, write test markers manually) | `test/baremetal/e2e_hello_qemu.spl` | 49 |
| 202 | TODO | general | P3 | Test trap handling | `test/baremetal/riscv64_boot_spec.spl` | 53 |
| 203 | TODO | general | P3 | Test IDT in long mode | `test/baremetal/x86_64_boot_spec.spl` | 58 |
| 204 | TODO | general | P3 | Test section placement | `test/baremetal/x86_boot_spec.spl` | 73 |
| 205 | TODO | general | P3 | Test entry point | `test/baremetal/x86_boot_spec.spl` | 79 |
| 206 | TODO | general | P3 | Test interrupt delivery | `test/baremetal/x86_boot_spec.spl` | 95 |
| 207 | TODO | general | P3 | Implement actual resolution logic | `test/compiler/import_resolution_spec.spl` | 171 |
| 208 | TODO | general | P3 | Implement error expectation | `test/compiler/import_resolution_spec.spl` | 176 |
| 209 | TODO | general | P3 | Implement parser with warning capture | `test/compiler/import_resolution_spec.spl` | 181 |
| 210 | TODO | general | P3 | Enable these tests when running in compiled/JIT mode | `test/compiler/mir_opt_spec.spl` | 465 |
| 211 | TODO | general | P3 | Or fix interpreter to properly support class construction | `test/compiler/mir_opt_spec.spl` | 466 |
| 212 | TODO | general | P3 | Parse and verify the expression | `test/compiler/parser_await_spawn_spec.spl` | 42 |
| 213 | TODO | general | P3 | Implement when benchmark infrastructure is ready | `test/integration/cli_dispatch_spec.spl` | 172 |
| 214 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler_interpreter_integration_spec.spl` | 59 |
| 215 | TODO | general | P3 | Test function compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 66 |
| 216 | TODO | general | P3 | Test class compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 73 |
| 217 | TODO | general | P3 | Test struct compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 80 |
| 218 | TODO | general | P3 | Test enum compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 84 |
| 219 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 102 |
| 220 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 109 |
| 221 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 116 |
| 222 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 120 |
| 223 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler_interpreter_integration_spec.spl` | 124 |
| 224 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler_interpreter_integration_spec.spl` | 142 |
| 225 | TODO | general | P3 | Test return type inference | `test/integration/compiler_interpreter_integration_spec.spl` | 146 |
| 226 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler_interpreter_integration_spec.spl` | 150 |
| 227 | TODO | general | P3 | Test type error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 154 |
| 228 | TODO | general | P3 | Test recursive types | `test/integration/compiler_interpreter_integration_spec.spl` | 158 |
| 229 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 176 |
| 230 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 183 |
| 231 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 190 |
| 232 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler_interpreter_integration_spec.spl` | 197 |
| 233 | TODO | general | P3 | Test error suggestions | `test/integration/compiler_interpreter_integration_spec.spl` | 201 |
| 234 | TODO | general | P3 | Test import resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 219 |
| 235 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler_interpreter_integration_spec.spl` | 226 |
| 236 | TODO | general | P3 | Test circular import detection | `test/integration/compiler_interpreter_integration_spec.spl` | 230 |
| 237 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 237 |
| 238 | TODO | general | P3 | Test hot reload | `test/integration/compiler_interpreter_integration_spec.spl` | 241 |
| 239 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler_interpreter_integration_spec.spl` | 259 |
| 240 | TODO | general | P3 | Test cache eviction | `test/integration/compiler_interpreter_integration_spec.spl` | 268 |
| 241 | TODO | general | P3 | Test refcount management | `test/integration/compiler_interpreter_integration_spec.spl` | 272 |
| 242 | TODO | general | P3 | Test leak detection | `test/integration/compiler_interpreter_integration_spec.spl` | 276 |
| 243 | TODO | general | P3 | Test deep recursion | `test/integration/compiler_interpreter_integration_spec.spl` | 280 |
| 244 | TODO | general | P3 | Rewrite this test using standard describe/it syntax | `test/lib/std/features/compiler/note_sdn_feature_spec.spl` | 4 |
| 245 | TODO | general | P3 | Implement tests when Gherkin DSL is production-ready | `test/lib/std/features/compiler/note_sdn_feature_spec.spl` | 12 |
| 246 | TODO | general | P3 | Rewrite this test using standard describe/it syntax | `test/lib/std/features/generic_bytecode_spec.spl` | 4 |
| 247 | TODO | general | P3 | Implement tests when Gherkin DSL is production-ready | `test/lib/std/features/generic_bytecode_spec.spl` | 11 |
| 248 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/bugs/interpreter_bugs_spec.spl` | 64 |
| 249 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/bugs/interpreter_bugs_spec.spl` | 105 |
| 250 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/improvements/parser_improvements_spec.spl` | 170 |
| 251 | TODO | general | P3 | Fix SdnDocument mutation methods | `test/lib/std/system/sdn/file_io_spec.spl` | 144 |
| 252 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/lib/std/system/spec/matchers/spec_matchers_spec.spl` | 62 |
| 253 | TODO | general | P3 | Enable tests once native codegen is complete | `test/lib/std/unit/codegen/static_method_spec.spl` | 334 |
| 254 | TODO | general | P3 | Implement module creation | `test/lib/std/unit/compiler/generic_template_spec.spl` | 359 |
| 255 | TODO | general | P3 | These will be implemented once we can import compiler modules | `test/lib/std/unit/compiler/helpers.spl` | 12 |
| 256 | TODO | general | P3 | import compiler.lexer.Lexer | `test/lib/std/unit/compiler/helpers.spl` | 21 |
| 257 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 38 |
| 258 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 45 |
| 259 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 52 |
| 260 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 59 |
| 261 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 66 |
| 262 | TODO | general | P3 | Add items to caches first | `test/lib/std/unit/compiler/linker/obj_taker_spec.spl` | 395 |
| 263 | TODO | general | P3 | Use actual HirType construction from compiler.type_infer | `test/lib/std/unit/compiler/linker/obj_taker_spec.spl` | 544 |
| 264 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 214 |
| 265 | TODO | general | P3 | Add TypeRegistry validation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 357 |
| 266 | TODO | general | P3 | Create test template and type args | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 415 |
| 267 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 424 |
| 268 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 428 |
| 269 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 432 |
| 270 | TODO | general | P3 | Verify DI container passed to compilation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 436 |
| 271 | TODO | general | P3 | Create test SMF file | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 442 |
| 272 | TODO | general | P3 | Load same module twice | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 453 |
| 273 | TODO | general | P3 | Test hot reload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 457 |
| 274 | TODO | general | P3 | Load non-existent file | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 461 |
| 275 | TODO | general | P3 | Verify is_loaded() after load | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 465 |
| 276 | TODO | general | P3 | Load then unload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 476 |
| 277 | TODO | general | P3 | Verify symbols removed | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 480 |
| 278 | TODO | general | P3 | Verify reader.close() called | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 484 |
| 279 | TODO | general | P3 | Load, modify, reload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 495 |
| 280 | TODO | general | P3 | Verify new instance cached | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 499 |
| 281 | TODO | general | P3 | Load module with symbol, resolve it | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 524 |
| 282 | TODO | general | P3 | Enable JIT, resolve missing generic | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 538 |
| 283 | TODO | general | P3 | Resolve JIT symbol twice, verify cache hit | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 542 |
| 284 | TODO | general | P3 | Resolve Vec<i64> | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 553 |
| 285 | TODO | general | P3 | Verify ObjTaker.take_with_types called | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 557 |
| 286 | TODO | general | P3 | Verify mangled name in global_symbols | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 561 |
| 287 | TODO | general | P3 | Load modules, verify count | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 584 |
| 288 | TODO | general | P3 | Load modules, verify symbol count | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 588 |
| 289 | TODO | general | P3 | Load multiple modules, verify list | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 634 |
| 290 | TODO | general | P3 | Add assertion when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 311 |
| 291 | TODO | general | P3 | Add assertions when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 323 |
| 292 | TODO | general | P3 | Add assertions when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 352 |
| 293 | TODO | general | P3 | Test when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 400 |
| 294 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_eval_spec.spl` | 13 |
| 295 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_lower_spec.spl` | 13 |
| 296 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_module_spec.spl` | 13 |
| 297 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_types_spec.spl` | 13 |
| 298 | TODO | general | P3 | Implement process wait with timeout | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 101 |
| 299 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 142 |
| 300 | TODO | general | P3 | Implement stale lock detection in FileLock | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 325 |
| 301 | TODO | general | P3 | Simulate write failure (e.g., disk full) | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 443 |
| 302 | TODO | general | P3 | Implement after process spawning is verified | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 495 |
| 303 | TODO | general | P3 | Simulate read-only filesystem | `test/lib/std/unit/tooling/test_db_edge_cases_spec.spl` | 435 |
| 304 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/lib/std/unit/tooling/test_db_integrity_spec.spl` | 429 |
| 305 | TODO | general | P3 | Add memory profiling | `test/lib/std/unit/tooling/test_db_performance_spec.spl` | 469 |
| 306 | TODO | general | P3 | Add tests for custom literal prefixes when registry is integrated | `test/system/collections/custom_literal_spec.spl` | 25 |
| 307 | TODO | general | P3 | GPU intrinsics require kernel context (this.index()) - no surface syntax available | `test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl` | 1504 |
| 308 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 888 |
| 309 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 893 |
| 310 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 898 |
| 311 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 903 |
| 312 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/system/features/macros/macro_validation_spec.spl` | 221 |
| 313 | TODO | general | P3 | super keyword not yet implemented in interpreter | `test/system/features/parser_edge_cases_spec.spl` | 46 |
| 314 | TODO | general | P3 | Tuple destructuring in for loops has interpreter issues in test context | `test/system/features/parser/parser_control_flow_spec.spl` | 162 |
| 315 | TODO | general | P3 | Enum variant constructors have interpreter issues in test context | `test/system/features/parser/parser_control_flow_spec.spl` | 211 |
| 316 | TODO | general | P3 | Lambda default parameters not yet supported | `test/system/features/parser/parser_default_keyword_spec.spl` | 123 |
| 317 | TODO | general | P3 | Method chaining has interpreter issues - breaking into separate calls | `test/system/features/parser/parser_expressions_spec.spl` | 178 |
| 318 | TODO | general | P3 | Method chaining has interpreter issues - breaking into separate calls | `test/system/features/parser/parser_expressions_spec.spl` | 403 |
| 319 | TODO | general | P3 | Trait implementation with 'implements' keyword not yet supported | `test/system/features/parser/parser_static_keyword_spec.spl` | 220 |
| 320 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/system/features/primitive_types/primitive_types_spec.spl` | 66 |
| 321 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_cursor_spec.spl` | 16 |
| 322 | TODO | general | P3 | TreeSitterParser module loading issues - skip tests until fixed | `test/system/features/treesitter/treesitter_error_recovery_spec.spl` | 36 |
| 323 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_query_spec.spl` | 16 |
| 324 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_tree_spec.spl` | 16 |
| 325 | TODO | general | P3 | needs rt_dir_* syscall wrappers | `test/system/ffi/syscalls_test.spl` | 42 |
| 326 | TODO | general | P3 | needs rt_file_lock/unlock syscall wrappers | `test/system/ffi/syscalls_test.spl` | 46 |
| 327 | TODO | general | P3 | needs rt_process_run syscall wrappers | `test/system/ffi/syscalls_test.spl` | 50 |
| 328 | TODO | general | P3 | Implement import resolution from runtime | `doc/plan/04_dynamic_loading_library_2.md` | 316 |
| 329 | TODO | general | P3 | Next Session Priorities | `doc/TODO_NEXT_SESSION.md` | 1 |
| 330 | TODO | general | P3 | Remove `Any` Type from Compiler | `doc/todo/remove_any_type.md` | 1 |

