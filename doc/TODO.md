# TODO Tracking

**Total:** 384 items | **Open:** 384 | **Blocked:** 0

## By Priority

| Priority | Count |
|----------|-------|
| P0 | 0 |
| P1 | 0 |
| P2 | 0 |
| P3 | 384 |

## By Area

| Area | Count |
|------|-------|
| general | 384 |

## All TODOs

| # | Type | Area | Priority | Description | File | Line |
|---|------|------|----------|-------------|------|------|
| 0 | TODO | general | P3 | Implement did-you-mean suggestions | `src/app/cli/check.spl` | 126 |
| 1 | TODO | general | P3 | When SMF loader is available in Simple, load and execute directly | `src/app/cli/main.spl` | 394 |
| 2 | TODO | general | P3 | Trigger interpreter reload | `src/app/dap/adapter/local.spl` | 208 |
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
| 18 | TODO | general | P3 | Re-enable platform-specific command resolution when using full parser | `src/app/io/mod.spl` | 357 |
| 19 | TODO | general | P3 | Implement Windows timeout using PowerShell or .NET | `src/app/io/mod.spl` | 376 |
| 20 | TODO | general | P3 | Implement memory_bytes, cpu_seconds, max_fds, max_procs limits | `src/app/io/mod.spl` | 395 |
| 21 | TODO | general | P3 | When compiler modules can run in interpreter mode, use pure-Simple LLVM path: | `src/app/io/mod.spl` | 961 |
| 22 | TODO | general | P3 | Import and use BaremetalBuilder directly once module imports work | `src/app/io/mod.spl` | 985 |
| 23 | TODO | general | P3 | Import and use compiler.driver and compiler.backend.llvm_backend | `src/app/io/mod.spl` | 1019 |
| 24 | TODO | general | P3 | Implement semantic token generation | `src/app/lsp/handlers/semantic_tokens.spl` | 66 |
| 25 | TODO | general | P3 | Implement Lean 4 verification integration | `src/app/lsp/handlers/verification.spl` | 35 |
| 26 | TODO | general | P3 | Implement proper tree traversal with position comparison | `src/app/lsp/utils.spl` | 20 |
| 27 | TODO | general | P3 | Print to stdout | `src/app/mcp/fileio_main.spl` | 463 |
| 28 | TODO | general | P3 | Implement regex matching | `src/app/mcp/fileio_protection.spl` | 55 |
| 29 | TODO | general | P3 | Implement proper JSON argument extraction | `src/app/mcp/main.spl` | 623 |
| 30 | TODO | general | P3 | Use proper SPK format once FFI is ready | `src/app/package/build.spl` | 103 |
| 31 | TODO | general | P3 | Verify checksum when FFI is available | `src/app/package/verify.spl` | 67 |
| 32 | TODO | general | P3 | Implement serial port reading | `src/app/semihost/reader.spl` | 176 |
| 33 | TODO | general | P3 | Implement OpenOCD GDB RSP connection | `src/app/semihost/reader.spl` | 207 |
| 34 | TODO | general | P3 | Implement proper SMF parsing | `src/app/semihost/reader.spl` | 382 |
| 35 | TODO | general | P3 | Implement proper stdin reading | `src/app/semihost/reader.spl` | 404 |
| 36 | TODO | general | P3 | Use actual time | `src/app/semihost/reader.spl` | 410 |
| 37 | TODO | general | P3 | Implement proper ANSI stripping when rt_char_code FFI is available | `src/app/test_runner_new/test_runner_files.spl` | 17 |
| 38 | TODO | general | P3 | When rt_process_spawn_async is available, run truly in parallel | `src/app/test_runner_new/test_runner_parallel.spl` | 52 |
| 39 | TODO | general | P3 | Submit PR to index repo to set yanked=false | `src/app/yank/main.spl` | 79 |
| 40 | TODO | general | P3 | Submit PR to index repo to set yanked=true | `src/app/yank/main.spl` | 87 |
| 41 | TODO | general | P3 | Parse barriers option from named args | `src/compiler/attributes.spl` | 68 |
| 42 | TODO | general | P3 | Return proper default span | `src/compiler/backend/arm_asm.spl` | 146 |
| 43 | TODO | general | P3 | Use filesystem FFI | `src/compiler/backend/exhaustiveness_validator.spl` | 208 |
| 44 | TODO | general | P3 | Capture free variables | `src/compiler/backend/interpreter.spl` | 217 |
| 45 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 685 |
| 46 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 698 |
| 47 | TODO | general | P3 | Convert ptr to Simple string | `src/compiler/backend/interpreter.spl` | 704 |
| 48 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 715 |
| 49 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 727 |
| 50 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 740 |
| 51 | TODO | general | P3 | Convert ptr to Simple string | `src/compiler/backend/interpreter.spl` | 745 |
| 52 | TODO | general | P3 | Proper string ptr+len conversion | `src/compiler/backend/interpreter.spl` | 756 |
| 53 | TODO | general | P3 | Proper string conversion (ptr + len) | `src/compiler/backend/interpreter.spl` | 780 |
| 54 | TODO | general | P3 | Implement full conversion for Array, Dict, etc. | `src/compiler/backend/interpreter.spl` | 784 |
| 55 | TODO | general | P3 | Implement full type conversion for all Simple types | `src/compiler/backend/jit_interpreter.spl` | 228 |
| 56 | TODO | general | P3 | Pass floats as i64 bit pattern | `src/compiler/backend/jit_interpreter.spl` | 235 |
| 57 | TODO | general | P3 | Determine actual return type from function signature | `src/compiler/backend/jit_interpreter.spl` | 248 |
| 58 | TODO | general | P3 | Return proper default span | `src/compiler/backend/riscv_asm.spl` | 231 |
| 59 | TODO | general | P3 | Fix parse errors in backend/*.spl (runtime parser bugs) | `src/compiler/backend.spl` | 23 |
| 60 | TODO | general | P3 | Backends commented out due to parse errors | `src/compiler/backend.spl` | 36 |
| 61 | TODO | general | P3 | Backends commented out due to parse errors | `src/compiler/backend.spl` | 41 |
| 62 | TODO | general | P3 | Backend implementations commented out due to parse errors | `src/compiler/backend.spl` | 55 |
| 63 | TODO | general | P3 | Load expr into reg | `src/compiler/backend/x86_asm.spl` | 111 |
| 64 | TODO | general | P3 | Store reg into var | `src/compiler/backend/x86_asm.spl` | 116 |
| 65 | TODO | general | P3 | Return proper default span | `src/compiler/backend/x86_asm.spl` | 284 |
| 66 | TODO | general | P3 | Use rt_cli_get_args() | `src/compiler/baremetal/link_wrapper.spl` | 291 |
| 67 | TODO | general | P3 | Use rt_exit() | `src/compiler/baremetal/link_wrapper.spl` | 295 |
| 68 | TODO | general | P3 | Import from app.io | `src/compiler/baremetal/string_extractor.spl` | 245 |
| 69 | TODO | general | P3 | Import from app.io | `src/compiler/baremetal/table_codegen.spl` | 189 |
| 70 | TODO | general | P3 | Import from blocks.definition when available | `src/compiler/blocks/easy.spl` | 282 |
| 71 | TODO | general | P3 | Deep equality comparison | `src/compiler/blocks/testing.spl` | 352 |
| 72 | TODO | general | P3 | Call actual JSON parser from std.json | `src/compiler/blocks/utils.spl` | 36 |
| 73 | TODO | general | P3 | Call actual YAML parser | `src/compiler/blocks/utils.spl` | 54 |
| 74 | TODO | general | P3 | Call actual TOML parser | `src/compiler/blocks/utils.spl` | 66 |
| 75 | TODO | general | P3 | Call actual XML parser | `src/compiler/blocks/utils.spl` | 78 |
| 76 | TODO | general | P3 | Call actual CSV parser | `src/compiler/blocks/utils.spl` | 101 |
| 77 | TODO | general | P3 | Implement actual JSON validation | `src/compiler/blocks/utils.spl` | 561 |
| 78 | TODO | general | P3 | Implement dialect-specific validation | `src/compiler/blocks/utils.spl` | 566 |
| 79 | TODO | general | P3 | Implement proper import scanning | `src/compiler/build_native.spl` | 217 |
| 80 | TODO | general | P3 | Implement via FFI | `src/compiler/build_native.spl` | 229 |
| 81 | TODO | general | P3 | Implement switch | `src/compiler/codegen.spl` | 523 |
| 82 | TODO | general | P3 | Extract code before first await from func_body | `src/compiler/desugar/poll_generator.spl` | 156 |
| 83 | TODO | general | P3 | Extract return value from func_body | `src/compiler/desugar/poll_generator.spl` | 179 |
| 84 | TODO | general | P3 | Apply final computation from function body | `src/compiler/desugar/poll_generator.spl` | 319 |
| 85 | TODO | general | P3 | Implement proper liveness analysis | `src/compiler/desugar/suspension_analysis.spl` | 283 |
| 86 | TODO | general | P3 | Deserialize from SDN format | `src/compiler/driver/incremental.spl` | 138 |
| 87 | TODO | general | P3 | Serialize to SDN format | `src/compiler/driver/incremental.spl` | 143 |
| 88 | TODO | general | P3 | Add "did you mean?" suggestions by checking similar names | `src/compiler/error_formatter.spl` | 235 |
| 89 | TODO | general | P3 | Look up symbol name | `src/compiler/error_formatter.spl` | 453 |
| 90 | TODO | general | P3 | Report detailed errors when diagnostics system supports them | `src/compiler/hir_lowering/async.spl` | 183 |
| 91 | TODO | general | P3 | Implement proper structural equality | `src/compiler/hir_lowering/async.spl` | 497 |
| 92 | TODO | general | P3 | Parse and interpret | `src/compiler/init.spl` | 140 |
| 93 | TODO | general | P3 | Load and interpret file | `src/compiler/init.spl` | 144 |
| 94 | TODO | general | P3 | JIT compile and execute | `src/compiler/init.spl` | 159 |
| 95 | TODO | general | P3 | JIT compile and execute file | `src/compiler/init.spl` | 163 |
| 96 | TODO | general | P3 | Compile to native code | `src/compiler/init.spl` | 167 |
| 97 | TODO | general | P3 | Compile to object file | `src/compiler/init.spl` | 184 |
| 98 | TODO | general | P3 | Implement actual parsing | `src/compiler/init.spl` | 263 |
| 99 | TODO | general | P3 | Implement hex to char conversion | `src/compiler/lexer.spl` | 514 |
| 100 | TODO | general | P3 | Load actual templates from input SMF TemplateCode sections | `src/compiler/linker/lazy_instantiator.spl` | 183 |
| 101 | TODO | general | P3 | Implement proper relocation parsing to find references | `src/compiler/linker/link.spl` | 292 |
| 102 | TODO | general | P3 | Implement proper SMF writing | `src/compiler/linker/link.spl` | 422 |
| 103 | TODO | general | P3 | Load runtime symbols | `src/compiler/linker/mold.spl` | 287 |
| 104 | TODO | general | P3 | Implement SMF to object compilation | `src/compiler/linker/object_resolver.spl` | 133 |
| 105 | TODO | general | P3 | Implement proper template parsing | `src/compiler/linker/obj_taker.spl` | 561 |
| 106 | TODO | general | P3 | Implement directory scanning | `src/compiler/linker/smf_getter.spl` | 168 |
| 107 | TODO | general | P3 | Create SmfReaderImpl from in-memory data | `src/compiler/linker/smf_getter.spl` | 248 |
| 108 | TODO | general | P3 | Implement proper template parsing | `src/compiler/linker/smf_reader.spl` | 239 |
| 109 | TODO | general | P3 | Implement section table reading | `src/compiler/linker/smf_reader.spl` | 266 |
| 110 | TODO | general | P3 | Implement proper byte-to-char conversion | `src/compiler/linker/smf_reader.spl` | 345 |
| 111 | TODO | general | P3 | Implement proper SDN parsing | `src/compiler/linker/smf_reader.spl` | 359 |
| 112 | TODO | general | P3 | Real code generation | `src/compiler/loader/compiler_ffi.spl` | 162 |
| 113 | TODO | general | P3 | Real type checking | `src/compiler/loader/compiler_ffi.spl` | 202 |
| 114 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 403 |
| 115 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 421 |
| 116 | TODO | general | P3 | Real JSON parsing | `src/compiler/loader/compiler_ffi.spl` | 446 |
| 117 | TODO | general | P3 | Re-enable when mmap functions are available in app.io.mod | `src/compiler/loader/jit_instantiator.spl` | 10 |
| 118 | TODO | general | P3 | Add these functions to app.io.mod when implementing executable memory support | `src/compiler/loader/jit_instantiator.spl` | 12 |
| 119 | TODO | general | P3 | Load actual template bytes from SMF TemplateCode section | `src/compiler/loader/jit_instantiator.spl` | 360 |
| 120 | TODO | general | P3 | Compile via FFI (stub for now - actual implementation needs JSON serialization) | `src/compiler/loader/jit_instantiator.spl` | 372 |
| 121 | TODO | general | P3 | Implement proper SMF update | `src/compiler/loader/jit_instantiator.spl` | 427 |
| 122 | TODO | general | P3 | Add mmap functions to app.io.mod when implementing memory-mapped file support | `src/compiler/loader/smf_cache.spl` | 21 |
| 123 | TODO | general | P3 | Parse section table for accurate offsets | `src/compiler/loader/smf_cache.spl` | 82 |
| 124 | TODO | general | P3 | Parse section table and read section | `src/compiler/loader/smf_cache.spl` | 153 |
| 125 | TODO | general | P3 | Implement proper type checking | `src/compiler/mir_bitfield.spl` | 17 |
| 126 | TODO | general | P3 | Look up bitfield in symbol table | `src/compiler/mir_bitfield.spl` | 24 |
| 127 | TODO | general | P3 | Implement proper f64 to bits conversion | `src/compiler/mir_interpreter.spl` | 444 |
| 128 | TODO | general | P3 | Implement proper bits to f64 conversion | `src/compiler/mir_interpreter.spl` | 449 |
| 129 | TODO | general | P3 | Proper string handling | `src/compiler/mir_lowering.spl` | 278 |
| 130 | TODO | general | P3 | Proper iterator lowering | `src/compiler/mir_lowering.spl` | 560 |
| 131 | TODO | general | P3 | Add to set when set type available | `src/compiler/mir_opt/dce.spl` | 51 |
| 132 | TODO | general | P3 | Check set membership | `src/compiler/mir_opt/dce.spl` | 56 |
| 133 | TODO | general | P3 | Add to set | `src/compiler/mir_opt/dce.spl` | 61 |
| 134 | TODO | general | P3 | Check set membership | `src/compiler/mir_opt/dce.spl` | 66 |
| 135 | TODO | general | P3 | Implement proper liveness analysis | `src/compiler/mir_opt/dce.spl` | 231 |
| 136 | TODO | general | P3 | Implement recursive detection | `src/compiler/mir_opt/inline.spl` | 131 |
| 137 | TODO | general | P3 | Create copy instructions for argument binding | `src/compiler/mir_opt/inline.spl` | 204 |
| 138 | TODO | general | P3 | Replace return with assignment to call_dest | `src/compiler/mir_opt/inline.spl` | 212 |
| 139 | TODO | general | P3 | Implement proper local renaming | `src/compiler/mir_opt/inline.spl` | 235 |
| 140 | TODO | general | P3 | Implement actual inlining logic | `src/compiler/mir_opt/inline.spl` | 341 |
| 141 | TODO | general | P3 | Implement full module-level inlining | `src/compiler/mir_opt/inline.spl` | 391 |
| 142 | TODO | general | P3 | Display per-pass statistics | `src/compiler/mir_opt_integration.spl` | 115 |
| 143 | TODO | general | P3 | Implement iteration count analysis | `src/compiler/mir_opt/loop_opt.spl` | 91 |
| 144 | TODO | general | P3 | Implement full LICM algorithm | `src/compiler/mir_opt/loop_opt.spl` | 279 |
| 145 | TODO | general | P3 | Implement loop unrolling | `src/compiler/mir_opt/loop_opt.spl` | 337 |
| 146 | TODO | general | P3 | Implement strength reduction patterns | `src/compiler/mir_opt/loop_opt.spl` | 416 |
| 147 | TODO | general | P3 | Actually run the pass | `src/compiler/mir_opt/mod.spl` | 131 |
| 148 | TODO | general | P3 | Actually run the pass | `src/compiler/mir_opt/mod.spl` | 297 |
| 149 | TODO | general | P3 | Add serialization for all instruction types | `src/compiler/mir_serialization.spl` | 253 |
| 150 | TODO | general | P3 |  | `src/compiler/module_resolver/manifest.spl` | 442 |
| 151 | TODO | general | P3 | These should be proper FFI functions | `src/compiler/module_resolver/resolution.spl` | 302 |
| 152 | TODO | general | P3 | Proper FFI function | `src/compiler/module_resolver/resolution.spl` | 324 |
| 153 | TODO | general | P3 |  | `src/compiler/module_resolver/resolution.spl` | 460 |
| 154 | TODO | general | P3 | These should be proper FFI functions | `src/compiler/module_resolver/types.spl` | 431 |
| 155 | TODO | general | P3 | Proper FFI function | `src/compiler/module_resolver/types.spl` | 449 |
| 156 | TODO | general | P3 |  | `src/compiler/module_resolver/types.spl` | 511 |
| 157 | TODO | general | P3 | Use file I/O FFI when available | `src/compiler/monomorphize/deferred.spl` | 178 |
| 158 | TODO | general | P3 | Implement proper SMF parsing with loader | `src/compiler/monomorphize/deferred.spl` | 182 |
| 159 | TODO | general | P3 | Create minimal FunctionDef | `src/compiler/monomorphize/deferred.spl` | 286 |
| 160 | TODO | general | P3 | Use Monomorphizer.specialize_function when available | `src/compiler/monomorphize/deferred.spl` | 341 |
| 161 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 372 |
| 162 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 398 |
| 163 | TODO | general | P3 | Implement specialization | `src/compiler/monomorphize/deferred.spl` | 424 |
| 164 | TODO | general | P3 | Proper calculation using section table | `src/compiler/monomorphize/hot_reload.spl` | 302 |
| 165 | TODO | general | P3 | Implement proper SDN parsing | `src/compiler/monomorphize/hot_reload.spl` | 335 |
| 166 | TODO | general | P3 | Implement file_write_at FFI for offset writes | `src/compiler/monomorphize/hot_reload.spl` | 345 |
| 167 | TODO | general | P3 | Implement file_read_at FFI for offset reads | `src/compiler/monomorphize/hot_reload.spl` | 356 |
| 168 | TODO | general | P3 |  | `src/compiler/monomorphize/hot_reload.spl` | 561 |
| 169 | TODO | general | P3 | Resolve symbol to name properly | `src/compiler/monomorphize_integration.spl` | 248 |
| 170 | TODO | general | P3 |  | `src/compiler/monomorphize/metadata.spl` | 413 |
| 171 | TODO | general | P3 | Convert AST type to ConcreteType | `src/compiler/monomorphize/partition.spl` | 203 |
| 172 | TODO | general | P3 | Convert AST type to ConcreteType | `src/compiler/monomorphize/partition.spl` | 210 |
| 173 | TODO | general | P3 |  | `src/compiler/monomorphize/partition.spl` | 615 |
| 174 | TODO | general | P3 |  | `src/compiler/monomorphize/tracker.spl` | 506 |
| 175 | TODO | general | P3 | Full union support (would need ConcreteType.Union variant) | `src/compiler/monomorphize/util.spl` | 241 |
| 176 | TODO | general | P3 |  | `src/compiler/monomorphize/util.spl` | 502 |
| 177 | TODO | general | P3 | Add attributes field to Function struct | `src/compiler/parser_extensions.spl` | 272 |
| 178 | TODO | general | P3 | Parse interpolations | `src/compiler/parser.spl` | 1217 |
| 179 | TODO | general | P3 | Implement proper parsing | `src/compiler/parser.spl` | 2295 |
| 180 | TODO | general | P3 | Implement proper parsing | `src/compiler/parser_types.spl` | 734 |
| 181 | TODO | general | P3 | val hir = lower_to_hir(specialized) | `src/compiler/pipeline_fn.spl` | 52 |
| 182 | TODO | general | P3 | var mir = lower_to_mir(hir, contract_mode, di) | `src/compiler/pipeline_fn.spl` | 56 |
| 183 | TODO | general | P3 | val code = codegen_to_native(mir) | `src/compiler/pipeline_fn.spl` | 67 |
| 184 | TODO | general | P3 | Parse SDN manifest | `src/compiler/project.spl` | 81 |
| 185 | TODO | general | P3 | Parse TOML manifest (legacy) | `src/compiler/project.spl` | 85 |
| 186 | TODO | general | P3 | Full expression type inference requires type checker integration | `src/compiler/query_api.spl` | 280 |
| 187 | TODO | general | P3 | Implement enhanced trait method resolution | `src/compiler/resolve.spl` | 695 |
| 188 | TODO | general | P3 | Detect host platform | `src/compiler/smf_writer.spl` | 29 |
| 189 | TODO | general | P3 | Implement actual AST serialization (Phase 3) | `src/compiler/smf_writer.spl` | 353 |
| 190 | TODO | general | P3 | Implement full metadata serialization (Phase 3) | `src/compiler/smf_writer.spl` | 397 |
| 191 | TODO | general | P3 | Proper ELF/object parsing | `src/compiler/smf_writer.spl` | 478 |
| 192 | TODO | general | P3 | Add method signatures | `src/compiler/traits.spl` | 764 |
| 193 | TODO | general | P3 | Lower type_args when available | `src/compiler/type_infer/inference.spl` | 366 |
| 194 | TODO | general | P3 | Re-enable when using full parser that supports 'mod package.submodule' syntax | `src/compiler/type_infer.spl` | 113 |
| 195 | TODO | general | P3 | Properly map type parameters to type arguments | `src/compiler/type_infer/traits.spl` | 185 |
| 196 | TODO | general | P3 | Properly map bound.type_param to the corresponding type_arg | `src/compiler/type_infer/traits.spl` | 196 |
| 197 | TODO | general | P3 | Determine which trait defines this method | `src/compiler/type_infer/traits.spl` | 210 |
| 198 | TODO | general | P3 | Check pattern, bind variables | `src/compiler/type_system/bidirectional.spl` | 165 |
| 199 | TODO | general | P3 | Implement bidirectional variants for let bindings, etc. | `src/compiler/type_system/bidirectional.spl` | 395 |
| 200 | TODO | general | P3 | Bind pattern variables | `src/compiler/type_system/expr_infer.spl` | 234 |
| 201 | TODO | general | P3 | Get FString keys and validate dict argument | `src/compiler/type_system/expr_infer.spl` | 685 |
| 202 | TODO | general | P3 | Check pattern against subject type | `src/compiler/type_system/expr_infer.spl` | 752 |
| 203 | TODO | general | P3 | Bind pattern variables | `src/compiler/type_system/expr_infer.spl` | 753 |
| 204 | TODO | general | P3 | Handle size expression | `src/compiler/type_system/module_check.spl` | 450 |
| 205 | TODO | general | P3 | Check pattern against subject type | `src/compiler/type_system/stmt_check.spl` | 361 |
| 206 | TODO | general | P3 | Bind pattern variables | `src/compiler/type_system/stmt_check.spl` | 362 |
| 207 | TODO | general | P3 | Extract element type from iterable | `src/compiler/type_system/stmt_check.spl` | 381 |
| 208 | TODO | general | P3 | Implement calc step checking | `src/compiler/type_system/stmt_check.spl` | 514 |
| 209 | TODO | general | P3 | Track last expression type | `src/compiler/type_system/stmt_check.spl` | 564 |
| 210 | TODO | general | P3 | Check classes, structs, enums, traits, impls | `src/compiler/visibility_integration.spl` | 26 |
| 211 | TODO | general | P3 | Add more expression types as needed | `src/compiler/visibility_integration.spl` | 126 |
| 212 | TODO | general | P3 | Re-enable when parser supports mutable field updates | `src/lib/database/feature.spl` | 264 |
| 213 | TODO | general | P3 | Implement proper wait logic | `src/lib/execution/mod.spl` | 173 |
| 214 | TODO | general | P3 | Implement proper event handling | `src/lib/execution/mod.spl` | 204 |
| 215 | TODO | general | P3 | Print to stdout | `src/lib/hooks/stop.spl` | 154 |
| 216 | TODO | general | P3 | Read line from stdin | `src/lib/hooks/stop.spl` | 158 |
| 217 | TODO | general | P3 | Remove once interpreter supports static methods | `src/lib/pure/autograd.spl` | 92 |
| 218 | TODO | general | P3 | Merge back to generic PureTensor<T> once interpreter supports generics | `src/lib/pure/tensor_f64.spl` | 4 |
| 219 | TODO | general | P3 | Remove this file once interpreter supports: | `src/lib/pure/tensor_factory.spl` | 6 |
| 220 | TODO | general | P3 | Remove these once interpreter supports static methods on generic types | `src/lib/pure/tensor.spl` | 96 |
| 221 | TODO | general | P3 | Replace {variable} with actual values | `src/runtime/hooks.spl` | 455 |
| 222 | TODO | general | P3 | Implement request-response pattern | `src/std/actors/actor.spl` | 73 |
| 223 | TODO | general | P3 | Back-pressure handling | `src/std/actors/actor.spl` | 99 |
| 224 | TODO | general | P3 | Invoke method on actor_instance | `src/std/actors/actor.spl` | 182 |
| 225 | TODO | general | P3 | Call cleanup hooks | `src/std/actors/actor.spl` | 214 |
| 226 | TODO | general | P3 | Integrate with timer | `src/std/async_host/combinators.spl` | 44 |
| 227 | TODO | general | P3 | Add compile-time runtime selection when conditional compilation is implemented | `src/std/async_unified.spl` | 16 |
| 228 | TODO | general | P3 | Use proper SDN parser here | `src/std/db_atomic.spl` | 351 |
| 229 | TODO | general | P3 | Parse content and update self.columns, self.rows | `src/std/db_atomic.spl` | 406 |
| 230 | TODO | general | P3 | Implement generational collection | `src/std/gc.spl` | 356 |
| 231 | TODO | general | P3 | Use type information to find pointers | `src/std/gc.spl` | 429 |
| 232 | TODO | general | P3 | Call type-specific finalizer | `src/std/gc.spl` | 530 |
| 233 | FIXME | general | P3 | Should return Some(Arc(self.ptr)) but can't construct Arc/Rc | `src/std/rc.spl` | 260 |
| 234 | TODO | general | P3 | Implement proper module detection | `src/std/spec.spl` | 289 |
| 235 | TODO | general | P3 | Re-enable generic version after bootstrap generics support | `src/std/src/di.spl` | 174 |
| 236 | TODO | general | P3 | Execute HIR via instruction module | `src/std/src/di.spl` | 344 |
| 237 | TODO | general | P3 | Implement via FFI to Rust codegen | `src/std/src/di.spl` | 363 |
| 238 | TODO | general | P3 | Implement via FFI | `src/std/src/di.spl` | 465 |
| 239 | TODO | general | P3 | Implement via FFI | `src/std/src/di.spl` | 481 |
| 240 | TODO | general | P3 | Re-enable generic version after bootstrap generics support | `src/std/src/di.spl` | 647 |
| 241 | TODO | general | P3 | Parse SDN artifacts file | `src/std/src/exp/artifact.spl` | 153 |
| 242 | TODO | general | P3 | Use rt_sdn_parse | `src/std/src/exp/config.spl` | 426 |
| 243 | TODO | general | P3 | Use proper FFI when available | `src/std/src/exp/config.spl` | 437 |
| 244 | TODO | general | P3 | Wire to Rust FFI check | `src/std/src/math/backend.spl` | 115 |
| 245 | TODO | general | P3 | Wire to Rust FFI check | `src/std/src/math/backend.spl` | 120 |
| 246 | TODO | general | P3 | Native backend implementation | `src/std/src/tensor/factory.spl` | 236 |
| 247 | TODO | general | P3 | Return actual dtype from handle | `src/std/src/tensor.spl` | 111 |
| 248 | TODO | general | P3 | This assumes we have file write via fs or similar | `test/app/package/ffi_spec.spl` | 17 |
| 249 | TODO | general | P3 | Test interrupt enable | `test/baremetal/arm32_boot_spec.spl` | 81 |
| 250 | TODO | general | P3 | Test priority levels | `test/baremetal/arm32_boot_spec.spl` | 87 |
| 251 | TODO | general | P3 | Test SysTick | `test/baremetal/arm32_boot_spec.spl` | 103 |
| 252 | TODO | general | P3 | Test exception handling | `test/baremetal/arm64_boot_spec.spl` | 59 |
| 253 | TODO | general | P3 | String iteration (for now, write test markers manually) | `test/baremetal/e2e_hello_qemu.spl` | 49 |
| 254 | TODO | general | P3 | Test trap handling | `test/baremetal/riscv64_boot_spec.spl` | 53 |
| 255 | TODO | general | P3 | Test IDT in long mode | `test/baremetal/x86_64_boot_spec.spl` | 58 |
| 256 | TODO | general | P3 | Test section placement | `test/baremetal/x86_boot_spec.spl` | 73 |
| 257 | TODO | general | P3 | Test entry point | `test/baremetal/x86_boot_spec.spl` | 79 |
| 258 | TODO | general | P3 | Test interrupt delivery | `test/baremetal/x86_boot_spec.spl` | 95 |
| 259 | TODO | general | P3 | Implement actual resolution logic | `test/compiler/import_resolution_spec.spl` | 171 |
| 260 | TODO | general | P3 | Implement error expectation | `test/compiler/import_resolution_spec.spl` | 176 |
| 261 | TODO | general | P3 | Implement parser with warning capture | `test/compiler/import_resolution_spec.spl` | 181 |
| 262 | TODO | general | P3 | Enable these tests when running in compiled/JIT mode | `test/compiler/mir_opt_spec.spl` | 465 |
| 263 | TODO | general | P3 | Or fix interpreter to properly support class construction | `test/compiler/mir_opt_spec.spl` | 466 |
| 264 | TODO | general | P3 | Parse and verify the expression | `test/compiler/parser_await_spawn_spec.spl` | 42 |
| 265 | TODO | general | P3 | Implement when benchmark infrastructure is ready | `test/integration/cli_dispatch_spec.spl` | 172 |
| 266 | TODO | general | P3 | Implement when parser integration complete | `test/integration/compiler_interpreter_integration_spec.spl` | 59 |
| 267 | TODO | general | P3 | Test function compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 66 |
| 268 | TODO | general | P3 | Test class compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 73 |
| 269 | TODO | general | P3 | Test struct compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 80 |
| 270 | TODO | general | P3 | Test enum compilation | `test/integration/compiler_interpreter_integration_spec.spl` | 84 |
| 271 | TODO | general | P3 | Test cross-module method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 102 |
| 272 | TODO | general | P3 | Test generic method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 109 |
| 273 | TODO | general | P3 | Test trait method resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 116 |
| 274 | TODO | general | P3 | Test UFCS resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 120 |
| 275 | TODO | general | P3 | Test ambiguity detection | `test/integration/compiler_interpreter_integration_spec.spl` | 124 |
| 276 | TODO | general | P3 | Test type inference for val bindings | `test/integration/compiler_interpreter_integration_spec.spl` | 142 |
| 277 | TODO | general | P3 | Test return type inference | `test/integration/compiler_interpreter_integration_spec.spl` | 146 |
| 278 | TODO | general | P3 | Test generic type argument inference | `test/integration/compiler_interpreter_integration_spec.spl` | 150 |
| 279 | TODO | general | P3 | Test type error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 154 |
| 280 | TODO | general | P3 | Test recursive types | `test/integration/compiler_interpreter_integration_spec.spl` | 158 |
| 281 | TODO | general | P3 | Test parse error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 176 |
| 282 | TODO | general | P3 | Test compilation error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 183 |
| 283 | TODO | general | P3 | Test runtime error reporting | `test/integration/compiler_interpreter_integration_spec.spl` | 190 |
| 284 | TODO | general | P3 | Test span/location in errors | `test/integration/compiler_interpreter_integration_spec.spl` | 197 |
| 285 | TODO | general | P3 | Test error suggestions | `test/integration/compiler_interpreter_integration_spec.spl` | 201 |
| 286 | TODO | general | P3 | Test import resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 219 |
| 287 | TODO | general | P3 | Test private symbol hiding | `test/integration/compiler_interpreter_integration_spec.spl` | 226 |
| 288 | TODO | general | P3 | Test circular import detection | `test/integration/compiler_interpreter_integration_spec.spl` | 230 |
| 289 | TODO | general | P3 | Test dependency graph resolution | `test/integration/compiler_interpreter_integration_spec.spl` | 237 |
| 290 | TODO | general | P3 | Test hot reload | `test/integration/compiler_interpreter_integration_spec.spl` | 241 |
| 291 | TODO | general | P3 | Test scope cleanup | `test/integration/compiler_interpreter_integration_spec.spl` | 259 |
| 292 | TODO | general | P3 | Test cache eviction | `test/integration/compiler_interpreter_integration_spec.spl` | 268 |
| 293 | TODO | general | P3 | Test refcount management | `test/integration/compiler_interpreter_integration_spec.spl` | 272 |
| 294 | TODO | general | P3 | Test leak detection | `test/integration/compiler_interpreter_integration_spec.spl` | 276 |
| 295 | TODO | general | P3 | Test deep recursion | `test/integration/compiler_interpreter_integration_spec.spl` | 280 |
| 296 | TODO | general | P3 | Rewrite this test using standard describe/it syntax | `test/lib/std/features/compiler/note_sdn_feature_spec.spl` | 4 |
| 297 | TODO | general | P3 | Implement tests when Gherkin DSL is production-ready | `test/lib/std/features/compiler/note_sdn_feature_spec.spl` | 12 |
| 298 | TODO | general | P3 | Rewrite this test using standard describe/it syntax | `test/lib/std/features/generic_bytecode_spec.spl` | 4 |
| 299 | TODO | general | P3 | Implement tests when Gherkin DSL is production-ready | `test/lib/std/features/generic_bytecode_spec.spl` | 11 |
| 300 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/bugs/interpreter_bugs_spec.spl` | 64 |
| 301 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/bugs/interpreter_bugs_spec.spl` | 105 |
| 302 | TODO | general | P3 | use statements inside it blocks cause stack overflow | `test/lib/std/system/improvements/parser_improvements_spec.spl` | 170 |
| 303 | TODO | general | P3 | Fix SdnDocument mutation methods | `test/lib/std/system/sdn/file_io_spec.spl` | 144 |
| 304 | TODO | general | P3 | Fix include matcher - currently returns Matcher(Exact(...)) instead of IncludeMatcher | `test/lib/std/system/spec/matchers/spec_matchers_spec.spl` | 62 |
| 305 | TODO | general | P3 | Enable tests once native codegen is complete | `test/lib/std/unit/codegen/static_method_spec.spl` | 334 |
| 306 | TODO | general | P3 | Implement module creation | `test/lib/std/unit/compiler/generic_template_spec.spl` | 359 |
| 307 | TODO | general | P3 | These will be implemented once we can import compiler modules | `test/lib/std/unit/compiler/helpers.spl` | 12 |
| 308 | TODO | general | P3 | import compiler.lexer.Lexer | `test/lib/std/unit/compiler/helpers.spl` | 21 |
| 309 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 38 |
| 310 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 45 |
| 311 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 52 |
| 312 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 59 |
| 313 | TODO | general | P3 | implement | `test/lib/std/unit/compiler/helpers.spl` | 66 |
| 314 | TODO | general | P3 | Add items to caches first | `test/lib/std/unit/compiler/linker/obj_taker_spec.spl` | 395 |
| 315 | TODO | general | P3 | Use actual HirType construction from compiler.type_infer | `test/lib/std/unit/compiler/linker/obj_taker_spec.spl` | 544 |
| 316 | TODO | general | P3 | Verify TypeRegistry.empty() properties | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 214 |
| 317 | TODO | general | P3 | Add TypeRegistry validation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 357 |
| 318 | TODO | general | P3 | Create test template and type args | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 415 |
| 319 | TODO | general | P3 | Verify compile_specialized_template called with ContractMode.Boundary | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 424 |
| 320 | TODO | general | P3 | Verify compile_specialized_template called with coverage=false | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 428 |
| 321 | TODO | general | P3 | Verify AOP weaver passed to compilation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 432 |
| 322 | TODO | general | P3 | Verify DI container passed to compilation | `test/lib/std/unit/compiler/loader/jit_context_spec.spl` | 436 |
| 323 | TODO | general | P3 | Create test SMF file | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 442 |
| 324 | TODO | general | P3 | Load same module twice | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 453 |
| 325 | TODO | general | P3 | Test hot reload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 457 |
| 326 | TODO | general | P3 | Load non-existent file | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 461 |
| 327 | TODO | general | P3 | Verify is_loaded() after load | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 465 |
| 328 | TODO | general | P3 | Load then unload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 476 |
| 329 | TODO | general | P3 | Verify symbols removed | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 480 |
| 330 | TODO | general | P3 | Verify reader.close() called | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 484 |
| 331 | TODO | general | P3 | Load, modify, reload | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 495 |
| 332 | TODO | general | P3 | Verify new instance cached | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 499 |
| 333 | TODO | general | P3 | Load module with symbol, resolve it | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 524 |
| 334 | TODO | general | P3 | Enable JIT, resolve missing generic | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 538 |
| 335 | TODO | general | P3 | Resolve JIT symbol twice, verify cache hit | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 542 |
| 336 | TODO | general | P3 | Resolve Vec<i64> | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 553 |
| 337 | TODO | general | P3 | Verify ObjTaker.take_with_types called | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 557 |
| 338 | TODO | general | P3 | Verify mangled name in global_symbols | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 561 |
| 339 | TODO | general | P3 | Load modules, verify count | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 584 |
| 340 | TODO | general | P3 | Load modules, verify symbol count | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 588 |
| 341 | TODO | general | P3 | Load multiple modules, verify list | `test/lib/std/unit/compiler/loader/module_loader_spec.spl` | 634 |
| 342 | TODO | general | P3 | Add assertion when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 311 |
| 343 | TODO | general | P3 | Add assertions when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 323 |
| 344 | TODO | general | P3 | Add assertions when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 352 |
| 345 | TODO | general | P3 | Test when interpreter integration is complete | `test/lib/std/unit/dap/interpreter_hooks_spec.spl` | 400 |
| 346 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_eval_spec.spl` | 13 |
| 347 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_lower_spec.spl` | 13 |
| 348 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_module_spec.spl` | 13 |
| 349 | TODO | general | P3 | Enable when hir module is ready for import | `test/lib/std/unit/hir/hir_types_spec.spl` | 13 |
| 350 | TODO | general | P3 | Implement process wait with timeout | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 101 |
| 351 | TODO | general | P3 | Implement after process spawning FFI is verified | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 142 |
| 352 | TODO | general | P3 | Implement stale lock detection in FileLock | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 325 |
| 353 | TODO | general | P3 | Simulate write failure (e.g., disk full) | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 443 |
| 354 | TODO | general | P3 | Implement after process spawning is verified | `test/lib/std/unit/tooling/test_db_concurrency_spec.spl` | 495 |
| 355 | TODO | general | P3 | Simulate read-only filesystem | `test/lib/std/unit/tooling/test_db_edge_cases_spec.spl` | 435 |
| 356 | TODO | general | P3 | Implement after adding TestDatabase.validate_all() and cleanup methods | `test/lib/std/unit/tooling/test_db_integrity_spec.spl` | 429 |
| 357 | TODO | general | P3 | Add memory profiling | `test/lib/std/unit/tooling/test_db_performance_spec.spl` | 469 |
| 358 | TODO | general | P3 | Slicing syntax needs investigation | `test/std/collections_spec.spl` | 29 |
| 359 | TODO | general | P3 | Add tests for custom literal prefixes when registry is integrated | `test/system/collections/custom_literal_spec.spl` | 25 |
| 360 | TODO | general | P3 | GPU intrinsics require kernel context (this.index()) - no surface syntax available | `test/system/features/codegen_parity_completion/codegen_parity_completion_spec.spl` | 1504 |
| 361 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 888 |
| 362 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 893 |
| 363 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 898 |
| 364 | TODO | general | P3 | Implement async operations when Task type is available | `test/system/features/database_synchronization/database_sync_spec.spl` | 903 |
| 365 | TODO | general | P3 | Multi-intro macro gensym creates suffixed names (var1_gensym_1) | `test/system/features/macros/macro_validation_spec.spl` | 221 |
| 366 | TODO | general | P3 | super keyword not yet implemented in interpreter | `test/system/features/parser_edge_cases_spec.spl` | 46 |
| 367 | TODO | general | P3 | Tuple destructuring in for loops has interpreter issues in test context | `test/system/features/parser/parser_control_flow_spec.spl` | 162 |
| 368 | TODO | general | P3 | Enum variant constructors have interpreter issues in test context | `test/system/features/parser/parser_control_flow_spec.spl` | 211 |
| 369 | TODO | general | P3 | Lambda default parameters not yet supported | `test/system/features/parser/parser_default_keyword_spec.spl` | 123 |
| 370 | TODO | general | P3 | Method chaining has interpreter issues - breaking into separate calls | `test/system/features/parser/parser_expressions_spec.spl` | 178 |
| 371 | TODO | general | P3 | Method chaining has interpreter issues - breaking into separate calls | `test/system/features/parser/parser_expressions_spec.spl` | 403 |
| 372 | TODO | general | P3 | Trait implementation with 'implements' keyword not yet supported | `test/system/features/parser/parser_static_keyword_spec.spl` | 220 |
| 373 | TODO | general | P3 | Type-based pattern matching on union types not yet implemented | `test/system/features/primitive_types/primitive_types_spec.spl` | 66 |
| 374 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_cursor_spec.spl` | 16 |
| 375 | TODO | general | P3 | TreeSitterParser module loading issues - skip tests until fixed | `test/system/features/treesitter/treesitter_error_recovery_spec.spl` | 36 |
| 376 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_query_spec.spl` | 16 |
| 377 | TODO | general | P3 | TreeSitterParser causes crashes - skip tests until fixed | `test/system/features/treesitter/treesitter_tree_spec.spl` | 16 |
| 378 | TODO | general | P3 | needs rt_dir_* syscall wrappers | `test/system/ffi/syscalls_test.spl` | 42 |
| 379 | TODO | general | P3 | needs rt_file_lock/unlock syscall wrappers | `test/system/ffi/syscalls_test.spl` | 46 |
| 380 | TODO | general | P3 | needs rt_process_run syscall wrappers | `test/system/ffi/syscalls_test.spl` | 50 |
| 381 | TODO | general | P3 | Implement import resolution from runtime | `doc/plan/04_dynamic_loading_library_2.md` | 316 |
| 382 | TODO | general | P3 | Next Session Priorities | `doc/TODO_NEXT_SESSION.md` | 1 |
| 383 | TODO | general | P3 | Remove `Any` Type from Compiler | `doc/todo/remove_any_type.md` | 1 |

