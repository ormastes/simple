# TODO Tracking

**Total:** 269 items | **Open:** 269 | **Blocked:** 0

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 0 |
| P1 | 0 |
| P2 | 0 |
| P3 | 269 |

## By Area

| Area | Count |
|------|-------|
| general | 269 |

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | When SMF loader is available in Simple, load and execute directly | `src/app/cli/main.spl` | 394 |
| 1 | TODO | general | P3 | Import and use parallel.spl and incremental.spl | `src/app/duplicate_check/detector.spl` | 438 |
| 2 | TODO | general | P3 | Parallel processing implementation | `src/app/duplicate_check/parallel.spl` | 42 |
| 3 | TODO | general | P3 | send DOWN message | `src/app/interpreter/async_runtime/actor_scheduler.spl` | 543 |
| 4 | TODO | general | P3 | Remove these once static method calls are supported in interpreter | `src/app/interpreter/collections/persistent_dict.spl` | 35 |
| 5 | TODO | general | P3 | Re-enable when collections module is complete | `src/app/interpreter/core/environment.spl` | 12 |
| 6 | TODO | general | P3 | Re-enable when complete | `src/app/interpreter/core/eval.spl` | 10 |
| 7 | TODO | general | P3 | Re-enable when Lazy and PersistentDict are complete | `src/app/interpreter/core/eval.spl` | 20 |
| 8 | TODO | general | P3 | Re-enable when Lazy and PersistentDict are complete | `src/app/interpreter/core/eval.spl` | 39 |
| 9 | TODO | general | P3 | Re-enable when RuntimeValue.Tensor variant is added | `src/app/interpreter/expr/__init__.spl` | 269 |
| 10 | TODO | general | P3 | Re-enable when AST construction syntax is fixed | `src/app/interpreter/helpers/macros.spl` | 251 |
| 11 | TODO | general | P3 | Re-enable platform-specific command resolution when using full parser | `src/app/io/mod.spl` | 505 |
| 12 | TODO | general | P3 | Implement Windows timeout using PowerShell or .NET | `src/app/io/mod.spl` | 524 |
| 13 | TODO | general | P3 | Implement memory_bytes, cpu_seconds, max_fds, max_procs limits | `src/app/io/mod.spl` | 543 |
| 14 | TODO | general | P3 | When compiler modules can run in interpreter mode, use pure-Simple LLVM path: | `src/app/io/mod.spl` | 1109 |
| 15 | TODO | general | P3 | Import and use BaremetalBuilder directly once module imports work | `src/app/io/mod.spl` | 1133 |
| 16 | TODO | general | P3 | Import and use compiler.driver and compiler.backend.llvm_backend | `src/app/io/mod.spl` | 1167 |
| 17 | TODO | general | P3 | Implement Lean 4 verification integration | `src/app/lsp/handlers/verification.spl` | 35 |
| 18 | TODO | general | P3 | Use proper SPK format once FFI is ready | `src/app/package/build.spl` | 103 |
| 19 | TODO | general | P3 | Verify checksum when FFI is available | `src/app/package/verify.spl` | 67 |
| 20 | TODO | general | P3 | Implement serial port reading | `src/app/semihost/reader.spl` | 176 |
| 21 | TODO | general | P3 | Implement OpenOCD GDB RSP connection | `src/app/semihost/reader.spl` | 207 |
| 22 | TODO | general | P3 | Implement proper SMF parsing | `src/app/semihost/reader.spl` | 382 |
| 23 | TODO | general | P3 | Implement proper stdin reading | `src/app/semihost/reader.spl` | 404 |
| 24 | TODO | general | P3 | Use actual time | `src/app/semihost/reader.spl` | 410 |
| 25 | TODO | general | P3 | When rt_process_spawn_async is available, run truly in parallel | `src/app/test_runner_new/test_runner_parallel.spl` | 51 |
| 26 | TODO | general | P3 | Submit PR to index repo to set yanked=false | `src/app/yank/main.spl` | 79 |
| 27 | TODO | general | P3 | Submit PR to index repo to set yanked=true | `src/app/yank/main.spl` | 87 |
| 28 | TODO | general | P3 | Use filesystem FFI | `src/compiler/backend/exhaustiveness_validator.spl` | 208 |
| 29 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 690 |
| 30 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 703 |
| 31 | TODO | general | P3 | Convert ptr to Simple string | `src/compiler/backend/interpreter.spl` | 709 |
| 32 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 720 |
| 33 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 732 |
| 34 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 745 |
| 35 | TODO | general | P3 | Convert ptr to Simple string | `src/compiler/backend/interpreter.spl` | 750 |
| 36 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 761 |
| 37 | TODO | general | P3 | Proper string conversion (ptr + len) | `src/compiler/backend/interpreter.spl` | 785 |
| 38 | TODO | general | P3 | Implement full conversion for Array, Dict, etc. | `src/compiler/backend/interpreter.spl` | 789 |
| 39 | TODO | general | P3 | Fix parse errors in backend/*.spl (runtime parser bugs) | `src/compiler/backend.spl` | 23 |
| 40 | TODO | general | P3 | Backends commented out due to parse errors | `src/compiler/backend.spl` | 36 |
| 41 | TODO | general | P3 | Backends commented out due to parse errors | `src/compiler/backend.spl` | 41 |
| 42 | TODO | general | P3 | Backend implementations commented out due to parse errors | `src/compiler/backend.spl` | 55 |
| 43 | TODO | general | P3 | Use rt_cli_get_args() | `src/compiler/baremetal/link_wrapper.spl` | 291 |
| 44 | TODO | general | P3 | Use rt_exit() | `src/compiler/baremetal/link_wrapper.spl` | 295 |
| 45 | TODO | general | P3 | Implement via FFI | `src/compiler/build_native.spl` | 312 |
| 46 | TODO | general | P3 | Apply final computation from function body | `src/compiler/desugar/poll_generator.spl` | 330 |
| 47 | TODO | general | P3 | Implement actual parsing | `src/compiler/init.spl` | 290 |
| 48 | TODO | general | P3 | Load actual templates from input SMF TemplateCode sections | `src/compiler/linker/lazy_instantiator.spl` | 183 |
| 49 | TODO | general | P3 | Implement SMF to object compilation | `src/compiler/linker/object_resolver.spl` | 133 |
| 50 | TODO | general | P3 | Implement proper template parsing | `src/compiler/linker/obj_taker.spl` | 564 |
| 51 | TODO | general | P3 | Create SmfReaderImpl from in-memory data | `src/compiler/linker/smf_getter.spl` | 261 |
| 52 | TODO | general | P3 | Implement proper template parsing | `src/compiler/linker/smf_reader.spl` | 233 |
| 53 | TODO | general | P3 | Implement section table reading | `src/compiler/linker/smf_reader.spl` | 246 |
| 54 | TODO | general | P3 | Real code generation | `src/compiler/loader/compiler_ffi.spl` | 162 |
| 55 | TODO | general | P3 | Real type checking | `src/compiler/loader/compiler_ffi.spl` | 202 |
| 56 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 403 |
| 57 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 421 |
| 58 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 446 |
| 59 | TODO | general | P3 | Re-enable when mmap functions are available in app.io.mod | `src/compiler/loader/jit_instantiator.spl` | 10 |
| 60 | TODO | general | P3 | Add these functions to app.io.mod when implementing executable memory support | `src/compiler/loader/jit_instantiator.spl` | 12 |
| 61 | TODO | general | P3 | Load actual template bytes from SMF TemplateCode section | `src/compiler/loader/jit_instantiator.spl` | 360 |
| 62 | TODO | general | P3 | Compile via FFI (stub for now - actual implementation needs JSON serialization) | `src/compiler/loader/jit_instantiator.spl` | 372 |
| 63 | TODO | general | P3 | Implement proper SMF update | `src/compiler/loader/jit_instantiator.spl` | 427 |
| 64 | TODO | general | P3 | Add mmap functions to app.io.mod when implementing memory-mapped file support | `src/compiler/loader/smf_cache.spl` | 21 |
| 65 | TODO | general | P3 | Parse section table for accurate offsets | `src/compiler/loader/smf_cache.spl` | 82 |
| 66 | TODO | general | P3 | Parse section table and read section | `src/compiler/loader/smf_cache.spl` | 153 |
| 67 | TODO | general | P3 | Proper iterator lowering | `src/compiler/mir_lowering.spl` | 562 |
| 68 | TODO | general | P3 | Implement actual inlining logic | `src/compiler/mir_opt/inline.spl` | 406 |
| 69 | TODO | general | P3 | Implement full module-level inlining | `src/compiler/mir_opt/inline.spl` | 456 |
| 70 | TODO | general | P3 | Implement iteration count analysis | `src/compiler/mir_opt/loop_opt.spl` | 91 |
| 71 | TODO | general | P3 | Implement full LICM algorithm | `src/compiler/mir_opt/loop_opt.spl` | 291 |
| 72 | TODO | general | P3 | Implement loop unrolling | `src/compiler/mir_opt/loop_opt.spl` | 349 |
| 73 | TODO | general | P3 | Implement strength reduction patterns | `src/compiler/mir_opt/loop_opt.spl` | 428 |
| 74 | TODO | general | P3 |  | `src/compiler/module_resolver/manifest.spl` | 442 |
| 75 | TODO | general | P3 | These should be proper FFI functions | `src/compiler/module_resolver/resolution.spl` | 302 |
| 76 | TODO | general | P3 | Proper FFI function | `src/compiler/module_resolver/resolution.spl` | 324 |
| 77 | TODO | general | P3 |  | `src/compiler/module_resolver/resolution.spl` | 460 |
| 78 | TODO | general | P3 | These should be proper FFI functions | `src/compiler/module_resolver/types.spl` | 431 |
| 79 | TODO | general | P3 | Proper FFI function | `src/compiler/module_resolver/types.spl` | 449 |
| 80 | TODO | general | P3 |  | `src/compiler/module_resolver/types.spl` | 511 |
| 81 | TODO | general | P3 | Use file I/O FFI when available | `src/compiler/monomorphize/deferred.spl` | 178 |
| 82 | TODO | general | P3 | Implement proper SMF parsing with loader | `src/compiler/monomorphize/deferred.spl` | 182 |
| 83 | TODO | general | P3 | Create minimal FunctionDef | `src/compiler/monomorphize/deferred.spl` | 286 |
| 84 | TODO | general | P3 | Use Monomorphizer.specialize_function when available | `src/compiler/monomorphize/deferred.spl` | 341 |
| 85 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 372 |
| 86 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 398 |
| 87 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 424 |
| 88 | TODO | general | P3 | Proper calculation using section table | `src/compiler/monomorphize/hot_reload.spl` | 302 |
| 89 | TODO | general | P3 | Implement file_write_at FFI for offset writes | `src/compiler/monomorphize/hot_reload.spl` | 352 |
| 90 | TODO | general | P3 | Implement file_read_at FFI for offset reads | `src/compiler/monomorphize/hot_reload.spl` | 363 |
| 91 | TODO | general | P3 |  | `src/compiler/monomorphize/hot_reload.spl` | 568 |
| 92 | TODO | general | P3 |  | `src/compiler/monomorphize/metadata.spl` | 413 |
| 93 | TODO | general | P3 |  | `src/compiler/monomorphize/partition.spl` | 626 |
| 94 | TODO | general | P3 |  | `src/compiler/monomorphize/tracker.spl` | 506 |
| 95 | TODO | general | P3 | Full union support (would need ConcreteType.Union variant) | `src/compiler/monomorphize/util.spl` | 241 |
| 96 | TODO | general | P3 |  | `src/compiler/monomorphize/util.spl` | 502 |
| 97 | TODO | general | P3 | Implement proper parsing | `src/compiler/parser.spl` | 2321 |
| 98 | TODO | general | P3 | Implement proper parsing | `src/compiler/parser_types.spl` | 734 |
| 99 | TODO | general | P3 | Full expression type inference requires type checker integration | `src/compiler/query_api.spl` | 280 |
| 100 | TODO | general | P3 | Implement actual AST serialization (Phase 3) | `src/compiler/smf_writer.spl` | 354 |
| 101 | TODO | general | P3 | Implement full metadata serialization (Phase 3) | `src/compiler/smf_writer.spl` | 398 |
| 102 | TODO | general | P3 | Proper ELF/object parsing | `src/compiler/smf_writer.spl` | 479 |
| 103 | TODO | general | P3 | Re-enable when using full parser that supports 'mod package.submodule' syntax | `src/compiler/type_infer.spl` | 113 |
| 104 | TODO | general | P3 | Check pattern, bind variables | `src/compiler/type_system/bidirectional.spl` | 165 |
| 105 | TODO | general | P3 | Implement bidirectional variants for let bindings, etc. | `src/compiler/type_system/bidirectional.spl` | 395 |
| 106 | TODO | general | P3 | Re-enable when parser supports mutable field updates | `src/lib/database/feature.spl` | 264 |
| 107 | TODO | general | P3 | Print to stdout (Phase 3.4 - needs SFFI support for stdout) | `src/lib/hooks/stop.spl` | 154 |
| 108 | TODO | general | P3 | Read line from stdin (Phase 3.4 - needs SFFI support for stdin) | `src/lib/hooks/stop.spl` | 160 |
| 109 | TODO | general | P3 | Remove once interpreter supports static methods | `src/lib/pure/autograd.spl` | 92 |
| 110 | TODO | general | P3 | Merge back to generic PureTensor<T> once interpreter supports generics | `src/lib/pure/tensor_f64.spl` | 4 |
| 111 | TODO | general | P3 | Remove this file once interpreter supports: | `src/lib/pure/tensor_factory.spl` | 6 |
| 112 | TODO | general | P3 | Remove these once interpreter supports static methods on generic types | `src/lib/pure/tensor.spl` | 96 |
| 113 | TODO | general | P3 | Integration point - When debugger FFI is available: | `src/runtime/hooks.spl` | 493 |
| 114 | TODO | general | P3 | Invoke method on actor_instance | `src/lib/actors/actor.spl` | 190 |
| 115 | TODO | general | P3 | Add compile-time runtime selection when conditional compilation is implemented | `src/lib/async_unified.spl` | 16 |
| 116 | TODO | general | P3 | Return error or dummy stream | `src/lib/gpu/context.spl` | 174 |
| 117 | TODO | general | P3 | Use proper sizeof[T]() when available | `src/lib/gpu/memory.spl` | 34 |
| 118 | TODO | general | P3 | Implement upload via tensor operations | `src/lib/gpu/memory.spl` | 49 |
| 119 | TODO | general | P3 | Implement download via tensor operations | `src/lib/gpu/memory.spl` | 63 |
| 120 | TODO | general | P3 | Implement via tensor copy | `src/lib/gpu/memory.spl` | 82 |
| 121 | TODO | general | P3 | Create tensor on GPU device | `src/lib/gpu/memory.spl` | 114 |
| 122 | FIXME | general | P3 | Should return Some(Arc(self.ptr)) but can't construct Arc/Rc | `src/lib/rc.spl` | 260 |
| 123 | TODO | general | P3 | Re-enable generic version after bootstrap generics support | `src/lib/src/di.spl` | 174 |
| 124 | TODO | general | P3 | Execute HIR via instruction module | `src/lib/src/di.spl` | 344 |
| 125 | TODO | general | P3 | Implement via FFI to Rust codegen | `src/lib/src/di.spl` | 363 |
| 126 | TODO | general | P3 | Implement via FFI | `src/lib/src/di.spl` | 465 |
| 127 | TODO | general | P3 | Implement via FFI | `src/lib/src/di.spl` | 481 |
| 128 | TODO | general | P3 | Re-enable generic version after bootstrap generics support | `src/lib/src/di.spl` | 647 |
| 129 | TODO | general | P3 | Use proper FFI when available | `src/lib/src/exp/config.spl` | 438 |
| 130 | TODO | general | P3 | Wire to Rust FFI check | `src/lib/src/math/backend.spl` | 115 |
| 131 | TODO | general | P3 | Wire to Rust FFI check | `src/lib/src/math/backend.spl` | 120 |
| 132 | TODO | general | P3 | Native backend implementation | `src/lib/src/tensor/factory.spl` | 236 |
| 133 | TODO | general | P3 | Return actual dtype from handle | `src/lib/src/tensor.spl` | 111 |
| 134 | TODO | general | P3 | This assumes we have file write via fs or similar | `test/app/package/ffi_spec.spl` | 17 |
| 135 | TODO | general | P3 | Test interrupt enable | `test/baremetal/arm32_boot_spec.spl` | 81 |
| 136 | TODO | general | P3 | Test priority levels | `test/baremetal/arm32_boot_spec.spl` | 87 |
| 137 | TODO | general | P3 | Test SysTick | `test/baremetal/arm32_boot_spec.spl` | 103 |
| 138 | TODO | general | P3 | Test exception handling | `test/baremetal/arm64_boot_spec.spl` | 59 |
| 139 | TODO | general | P3 | String iteration (for now, write test markers manually) | `test/baremetal/e2e_hello_qemu.spl` | 49 |
| 140 | TODO | general | P3 | Test trap handling | `test/baremetal/riscv64_boot_spec.spl` | 53 |
| 141 | TODO | general | P3 | Test IDT in long mode | `test/baremetal/x86_64_boot_spec.spl` | 58 |
| 142 | TODO | general | P3 | Test section placement | `test/baremetal/x86_boot_spec.spl` | 73 |
| 143 | TODO | general | P3 | Test entry point | `test/baremetal/x86_boot_spec.spl` | 79 |
| 144 | TODO | general | P3 | Test interrupt delivery | `test/baremetal/x86_boot_spec.spl` | 95 |
| 145 | TODO | general | P3 | Implement actual resolution logic | `test/compiler/import_resolution_spec.spl` | 171 |
| 146 | TODO | general | P3 | Implement error expectation | `test/compiler/import_resolution_spec.spl` | 176 |
| 147 | TODO | general | P3 | Implement parser with warning capture | `test/compiler/import_resolution_spec.spl` | 181 |
| 148 | TODO | general | P3 | Enable these tests when running in compiled/JIT mode | `test/compiler/mir_opt_spec.spl` | 465 |
| 149 | TODO | general | P3 | Or fix interpreter to properly support class construction | `test/compiler/mir_opt_spec.spl` | 466 |
| 150 | TODO | general | P3 | Parse and verify the expression | `test/compiler/parser_await_spawn_spec.spl` | 42 |
| 151 | TODO | general | P3 | Implement when benchmark infrastructure is ready | `test/integration/cli_dispatch_spec.spl` | 172 |
| 152 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler_interpreter_integration_spec.spl` | 59 |
| 153 | TODO | general | P3 | Test function compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 66 |
| 154 | TODO | general | P3 | Test class compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 73 |
| 155 | TODO | general | P3 | Test struct compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 80 |
| 156 | TODO | general | P3 | Test enum compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 84 |
| 157 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 102 |
| 158 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 109 |
| 159 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 116 |
| 160 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 120 |
| 161 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler_interpreter_integration_spec.spl` | 124 |
| 162 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler_interpreter_integration_spec.spl` | 142 |
| 163 | TODO | general | P3 | Test return type inference | `test/integration/compiler_interpreter_integration_spec.spl` | 146 |
| 164 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler_interpreter_integration_spec.spl` | 150 |
| 165 | TODO | general | P3 | Test type error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 154 |
| 166 | TODO | general | P3 | Test recursive types | `test/integration/compiler_interpreter_integration_spec.spl` | 158 |
| 167 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 176 |
| 168 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 183 |
| 169 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 190 |
| 170 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler_interpreter_integration_spec.spl` | 197 |
| 171 | TODO | general | P3 | Test error suggestions | `test/integration/compiler_interpreter_integration_spec.spl` | 201 |
| 172 | TODO | general | P3 | Test import resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 219 |
| 173 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler_interpreter_integration_spec.spl` | 226 |
| 174 | TODO | general | P3 | Test circular import detection | `test/integration/compiler_interpreter_integration_spec.spl` | 230 |
| 175 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 237 |
| 176 | TODO | general | P3 | Test hot reload | `test/integration/compiler_interpreter_integration_spec.spl` | 241 |
| 177 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler_interpreter_integration_spec.spl` | 259 |
| 178 | TODO | general | P3 | Test cache eviction | `test/integration/compiler_interpreter_integration_spec.spl` | 268 |
| 179 | TODO | general | P3 | Test refcount management | `test/integration/compiler_interpreter_integration_spec.spl` | 272 |
| 180 | TODO | general | P3 | Test leak detection | `test/integration/compiler_interpreter_integration_spec.spl` | 276 |
| 181 | TODO | general | P3 | Test deep recursion | `test/integration/compiler_interpreter_integration_spec.spl` | 280 |
| 182 | TODO | general | P3 | Rewrite this test using standard describe/it syntax | `test/lib/std/features/compiler/note_sdn_feature_spec.spl` | 4 |
| 183 | TODO | general | P3 | Implement tests when Gherkin DSL is production-ready | `test/lib/std/features/compiler/note_sdn_feature_spec.spl` | 12 |
| 184 | TODO | general | P3 | Rewrite this test using standard describe/it syntax | `test/lib/std/features/generic_bytecode_spec.spl` | 4 |
| 185 | TODO | general | P3 | Implement tests when Gherkin DSL is production-ready | `test/lib/std/features/generic_bytecode_spec.spl` | 11 |
| 186 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/bugs/interpreter_bugs_spec.spl` | 64 |
| 187 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/bugs/interpreter_bugs_spec.spl` | 105 |
| 188 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/improvements/parser_improvements_spec.spl` | 170 |
| 189 | TODO | general | P3 | Fix SdnDocument mutation methods | `test/lib/std/system/sdn/file_io_spec.spl` | 144 |
| 190 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/lib/std/system/spec/matchers/spec_matchers_spec.spl` | 62 |
| 191 | TODO | general | P3 | Enable tests once native codegen is complete | `test/lib/std/unit/codegen/static_method_spec.spl` | 334 |
| 192 | TODO | general | P3 | Implement module creation | `test/lib/std/unit/compiler/generic_template_spec.spl` | 359 |
| 193 | TODO | general | P3 | These will be implemented once we can import compiler modules | `test/lib/std/unit/compiler/helpers.spl` | 12 |
| 194 | TODO | general | P3 | import compiler.lexer.Lexer | `test/lib/std/unit/compiler/helpers.spl` | 21 |
| 195 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 38 |
| 196 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 45 |
| 197 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 52 |
| 198 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 59 |
| 199 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 66 |
| 200 | TODO | general | P3 | Add items to caches first | `test/lib/std/unit/compiler/linker/obj_taker_spec.spl` | 395 |
| 201 | TODO | general | P3 | Use actual HirType construction from compiler.type_infer | `test/lib/std/unit/compiler/linker/obj_taker_spec.spl` | 544 |
| 202 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 214 |
| 203 | TODO | general | P3 | Add TypeRegistry validation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 357 |
| 204 | TODO | general | P3 | Create test template and type args | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 415 |
| 205 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 424 |
| 206 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 428 |
| 207 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 432 |
| 208 | TODO | general | P3 | Verify DI container passed to compilation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 436 |
| 209 | TODO | general | P3 | Create test SMF file | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 442 |
| 210 | TODO | general | P3 | Load same module twice | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 453 |
| 211 | TODO | general | P3 | Test hot reload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 457 |
| 212 | TODO | general | P3 | Load non-existent file | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 461 |
| 213 | TODO | general | P3 | Verify is_loaded() after load | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 465 |
| 214 | TODO | general | P3 | Load then unload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 476 |
| 215 | TODO | general | P3 | Verify symbols removed | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 480 |
| 216 | TODO | general | P3 | Verify reader.close() called | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 484 |
| 217 | TODO | general | P3 | Load, modify, reload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 495 |
| 218 | TODO | general | P3 | Verify new instance cached | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 499 |
| 219 | TODO | general | P3 | Load module with symbol, resolve it | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 524 |
| 220 | TODO | general | P3 | Enable JIT, resolve missing generic | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 538 |
| 221 | TODO | general | P3 | Resolve JIT symbol twice, verify cache hit | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 542 |
| 222 | TODO | general | P3 | Resolve Vec<i64> | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 553 |
| 223 | TODO | general | P3 | Verify ObjTaker.take_with_types called | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 557 |
| 224 | TODO | general | P3 | Verify mangled name in global_symbols | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 561 |
| 225 | TODO | general | P3 | Load modules, verify count | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 584 |
| 226 | TODO | general | P3 | Load modules, verify symbol count | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 588 |
| 227 | TODO | general | P3 | Load multiple modules, verify list | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 634 |
| 228 | TODO | general | P3 | Add assertion when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 311 |
| 229 | TODO | general | P3 | Add assertions when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 323 |
| 230 | TODO | general | P3 | Add assertions when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 352 |
| 231 | TODO | general | P3 | Test when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 400 |
| 232 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_eval_spec.spl` | 13 |
| 233 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_lower_spec.spl` | 13 |
| 234 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_module_spec.spl` | 13 |
| 235 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_types_spec.spl` | 13 |
| 236 | TODO | general | P3 | Implement process wait with timeout | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 101 |
| 237 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 142 |
| 238 | TODO | general | P3 | Implement stale lock detection in FileLock | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 325 |
| 239 | TODO | general | P3 | Simulate write failure (e.g., disk full) | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 443 |
| 240 | TODO | general | P3 | Implement after process spawning is verified | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 495 |
| 241 | TODO | general | P3 | Simulate read-only filesystem | `test/lib/std/unit/tooling/test_db_edge_cases_spec.spl` | 435 |
| 242 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/lib/std/unit/tooling/test_db_integrity_spec.spl` | 429 |
| 243 | TODO | general | P3 | Add memory profiling | `test/lib/std/unit/tooling/test_db_performance_spec.spl` | 469 |
| 244 | TODO | general | P3 | Add tests for custom literal prefixes when registry is integrated | `test/system/collections/custom_literal_spec.spl` | 25 |
| 245 | TODO | general | P3 | GPU intrinsics require kernel context (this.index()) - no surface syntax available | `test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl` | 1504 |
| 246 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 888 |
| 247 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 893 |
| 248 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 898 |
| 249 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 903 |
| 250 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/system/features/macros/macro_validation_spec.spl` | 221 |
| 251 | TODO | general | P3 | super keyword not yet implemented in interpreter | `test/system/features/parser_edge_cases_spec.spl` | 46 |
| 252 | TODO | general | P3 | Tuple destructuring in for loops has interpreter issues in test context | `test/system/features/parser/parser_control_flow_spec.spl` | 162 |
| 253 | TODO | general | P3 | Enum variant constructors have interpreter issues in test context | `test/system/features/parser/parser_control_flow_spec.spl` | 211 |
| 254 | TODO | general | P3 | Lambda default parameters not yet supported | `test/system/features/parser/parser_default_keyword_spec.spl` | 123 |
| 255 | TODO | general | P3 | Method chaining has interpreter issues - breaking into separate calls | `test/system/features/parser/parser_expressions_spec.spl` | 178 |
| 256 | TODO | general | P3 | Method chaining has interpreter issues - breaking into separate calls | `test/system/features/parser/parser_expressions_spec.spl` | 403 |
| 257 | TODO | general | P3 | Trait implementation with 'implements' keyword not yet supported | `test/system/features/parser/parser_static_keyword_spec.spl` | 220 |
| 258 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/system/features/primitive_types/primitive_types_spec.spl` | 66 |
| 259 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_cursor_spec.spl` | 16 |
| 260 | TODO | general | P3 | TreeSitterParser module loading issues - skip tests until fixed | `test/system/features/treesitter/treesitter_error_recovery_spec.spl` | 36 |
| 261 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_query_spec.spl` | 16 |
| 262 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_tree_spec.spl` | 16 |
| 263 | TODO | general | P3 | needs rt_dir_* syscall wrappers | `test/system/ffi/syscalls_test.spl` | 42 |
| 264 | TODO | general | P3 | needs rt_file_lock/unlock syscall wrappers | `test/system/ffi/syscalls_test.spl` | 46 |
| 265 | TODO | general | P3 | needs rt_process_run syscall wrappers | `test/system/ffi/syscalls_test.spl` | 50 |
| 266 | TODO | general | P3 | Implement import resolution from runtime | `doc/plan/04_dynamic_loading_library_2.md` | 316 |
| 267 | TODO | general | P3 | Next Session Priorities | `doc/TODO_NEXT_SESSION.md` | 1 |
| 268 | TODO | general | P3 | Remove `Any` Type from Compiler | `doc/todo/remove_any_type.md` | 1 |

