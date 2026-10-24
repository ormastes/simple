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
