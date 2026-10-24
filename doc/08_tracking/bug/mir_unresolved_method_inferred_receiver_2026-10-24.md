# MIR "unresolved method call" on receivers with inferred/unknown type (2026-10-24)

Symptom (Phase-3 run-11, stage=mir): `MIR lowering error: unresolved method call: <m>`.
The method is lowered to a const-0 placeholder (silent-null risk, Task #145), then the module fails.

Root cause: the pure-Simple MIR lowering resolves a method call from the receiver's *static MIR type*.
When the receiver is an inferred local (`val x = if ... else nil`), a chained call result
(`f(..).unwrap()`), an index result (`d[k]` then `.unwrap()`), a module `var` read, or a field whose
declared generic type did not resolve, the type is unknown and the call is not resolved.
Real fix location: `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` and friends
(receiver type inference for Option/Result/text/Dict methods; fall back to the declared type of the
callee/field/module var instead of giving up). Prior case: mir_text_bytes_unresolved_inferred_trim_receiver_2026-10-23.md.

## Sites (all workarounds tagged `@workaround bug=mir_unresolved_method_inferred_receiver_2026-10-24`)
| site | method | workaround |
|---|---|---|
| 70.backend/codegen.spl:592 | unwrap on `self.symbol_map[id]` | typed `text?` local + typed `text` local |
| 80.driver/driver_aot_native_output.spl:2387 | unwrap on `if..else nil` local | `val cached_outputs: [text]?` |
| 80.driver/driver_build/incremental.spl:285 | bytes on `substring` result | typed `text` local |
| 80.driver/driver_pipeline_lowering.spl:1397/1407 | is_err/unwrap/unwrap_err on `if val .. else Err(..)` | `Result<MirModule, text>` annotation |
| 10.frontend/frontend_shared_parse_cas_v1.spl:159 | get_or on module `var` Dict | typed `Dict<text, text>` local |
| 50.mir/hwir/mir_to_hwir.spl:330/331 | `strict_mir_local(..).unwrap()` chained (inferred; log has no line, 2 failures) | typed `MirLocal?` locals. Other unwraps in file not touched (unverified guess) |
| 70.backend/backend/env.spl:224-249 | process_module/is_allowed/eval_expr/... | NOT inference: `Backend` = `type Backend = CompilerBackend` which has none of these methods. `HirVisitor` struct was dead (never constructed), so it was deleted along with its exports in backend.spl and backend/__init__.spl |
| 20.hir/archive/interface_action_archive.spl:334 -> driver_source_pipeline_loading.spl:649 | is_err on `committed.result` | field type `Result[[X], Y]` rewritten to `Result<[X], Y>` (unverified; root cause hypothesis is the nested bracket generic) |

Not verified: no compile was run (memory budget reserved for run-11). Sites with unknown exact line
(driver_aot_native_output other unwraps, mir_to_hwir) may still fail; check the next run's log.

## Later sites (picked up while polling run-11)
| site | method | workaround |
|---|---|---|
| 70.backend/backend_plugin/loader.spl:45 | unwrap on `validated.err()` chain | typed `BackendPluginError?` local |
| 70.backend/backend/llvm_type_mapper.spl:284/:318 | `.map(self.f(_)).sum()/.max()` closure chain | explicit loops |
| 70.backend/../vulkan_type_mapper.spl:316 (plugins/backend_vulkan) | same `.sum()` | explicit loop |
| 30.types/type_infer/context.spl:136 | unwrap on `{i64: bool}` index | typed `bool?` local |
| 30.types/type_infer/generic_calls.spl:22 | unwrap on match-expression local | `SymbolId?` annotation |
| 50.mir/mir_bitfield.spl:23 | contains on `symbol.name` | typed `text` local |
| 70.backend/linker/mold.spl:447 | parse_i64 on `.trim()` result | typed `text` local |
| plugins/backend_lean/lean_type_declarations.spl:599,504 | `create` (declared `fn`, called statically: add `static`), `pop` on inferred `[start]` | `static fn`, typed `[i64]` locals |
| plugins/backend_vhdl/vhdl/vhdl_call_lowering.spl:790,819 | unwrap on `if .. else nil` local | `MirFunction?` annotation |

## NOT fixable by a source workaround
- 70.backend/linker/smf_getter.spl:337/340/371/372: `file_read` (std.nogc_sync_mut.io.file_ops:168) returns `text`, yet the code calls `.is_err()/.is_ok()/.unwrap()` on it. Genuine type error, not inference; fixing changes behavior (error path) and needs an owner decision (use a Result-returning read).

## Third batch
| site | cause | action |
|---|---|---|
| 70.backend/linker/lazy_instantiator.spl:188 | `self.do_instantiate` but the fn is the free `lazyinstantiator_do_instantiate(self, ..)` | call the free fn (fixed) |
| 70.backend/backend/native/isel_x86_64.spl:1110, 10.frontend/core/aop_debug_log.spl:114 | `.max()` on a parenthesized arithmetic expr | `if` expression with typed local (fixed) |
| 70.backend/bitfield.spl:193/218 (+269/284) | `HirType.to_text()` - no such method on HirType found | NOT fixed: needs a real text conversion fn |
| plugins/backend_cuda/cuda_type_mapper.spl:282 | `fields.len()` where `ty.kind` match binder; file imports only `MirType`, not `MirTypeKind`/`MirFieldDef` | NOT fixed |
| plugins/backend_llvm_lib/llvm_lib_translate_expr.spl:652/653 | `args.len()` on `val args: [MirOperand] = raw_args` (declared!) | NOT fixed: real MIR gap (array-typed local from i64 handle) |
| 70.backend/linker/link.spl, mold `parse_i` | unwrap with no line; parse_i64 site typed | link.spl unwrap not located |

## Run-12 batch (type_infer / driver / hwir)
| site | cause | action |
|---|---|---|
| 30.types/type_infer/inference_expr.spl SetLit | REAL bug: `HirTypeKind.Named("Set", ..)` passes text for `symbol: SymbolId` | new `set_type_symbol()` (looks up "Set" in `symbol_names`, else SymbolId(-1)); fix |
| inference_expr.spl, inference_effects.spl, inference_expr_ops.spl:140 | unwrap on pattern-bound optionals / `x.field.unwrap()` / index result | typed `T?` locals (workaround; exact failing line not in log, all candidates covered) |
| 80.driver/driver_aot_native_output.spl, driver_pipeline_lowering.spl | `go_to_end_finish_v1` / `native_staged_codegen_flush_v1` live in the `CompilerDriver` impl of driver_aot_pipeline.spl, which these modules did not import (siblings use `use compiler.driver.driver_aot_pipeline.*`) | added the glob import (fix; may add import cycle pipeline_lowering -> aot_pipeline -> driver_pipeline -> pipeline_lowering, unverified) |
| driver_aot_native_output.spl unwraps | body/bytes/persisted/phase2 manifest/decoded_key.key | typed locals (workaround) |
| 20.hir/archive/interface_action_archive.spl:328 | `Result[(), E]` bracket generic on `.result` -> is_err unresolved at driver_source_pipeline_loading:625 | `Result<(), E>` (fix, unverified) |
| 10.frontend/frontend_shared_parse_cas_v1.spl:161 | get_or still unresolved on typed Dict local | contains_key + index (workaround) |
| 50.mir/hwir/mir_to_hwir.spl | chained `strict_mir_*().unwrap().field` | typed `MirLocal?`/`LocalId?`/`HwirStrictLowerResult?` locals (workaround) |
| 50.mir/_MirLoweringExpr/expr_dispatch.spl:5134 | `.len()` on `_sffi_tuple_get<[HirIfArm]>` result | `[HirIfArm]?` local + `?? []` (workaround) |
Unverified: no compile run.
