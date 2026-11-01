# Stage2 -> stage3 workaround inventory (2026-11-01)

Scope: tagged workarounds that the frozen stage2 (`C:/dev/p3new/stage2.exe`, source ef0681fc0e1,
built 2026-10-27) needs to build stage3 from `release/1.0.0` (4de6127c67d). Source of truth:
`git grep -n -E '@workaround bug=|WORKAROUND\(stage2' origin/release/1.0.0` (1226 lines, about 200 ids).
This table covers the stage2/stage3 family (ids dated 2026-10-31 / 2026-11-01). Older native-seed
ids (2026-10-05 .. 2026-10-30) are tracked in their own bug files and are out of scope here.

Workarounds are NOT reverted by this lane. Reverting belongs to the phase 3 owner once a stage3
self-build succeeds. "revert-ready" means current source carries the real fix plus a regression
spec, so the tags can be dropped once the rebuilt producer is verified.

Status values: `fixed-in-source (<evidence>)`, `fixed (PR #n)`,
`spec+design only (PR #n)`, `stage2-only (no source bug)`.

| id | sites | real-fix owner file | status |
|---|---|---|---|
| eprint-noparen-stage2-20261031 | 32 (src/app/cli, src/app/verify, src/app/test) | src/compiler/10.frontend (parser, PR #5567) | fixed-in-source (50b383280c3; eprint_noparen_call_spec 3/3 seed; status PR #5769) |
| methods-mir-20261031 | 31 (lib/common/serialization, nogc_sync_mut/io, linker) | src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl (method receiver typing) | spec+design only (PR #5771, 7/7 seed): shapes 1-3 (untyped param substring/slice, no-return-type result .len, narrowed text?) still fail; 4-6 full-closure only. NOT revert-ready |
| enumowner-mir-20261031 | 25 (35.semantics/param_effects, async_ring, driver_build, backend) | src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl (bare-variant resolution) | spec only (PR #5772, 3/3 seed): all 3 shapes compile clean in reduced closure; full-closure only. revert-ready pending full stage3 build |
| rti007-mir-20261031 | 20 (70.backend/linker) | src/compiler/20.hir/return_type_interface_v1.spl | fixed-in-source (933a0979878; seed HIR/RTI fixture gives result(b:any,b:any), no E-RTI-007; MIR UNRUN; status PR #5776). revert-ready |
| rti007_any_return_rows_2026-11-01 | 77 (lib/common/serialization, concurrent, async) | src/compiler/20.hir/return_type_interface_v1.spl | fixed-in-source (all 5 producer commits present; seed RTI fixtures give rows; MIR UNRUN; status PR #5777). revert-ready (map_values<U> source fix stays) |
| inferarm-mir-20261031 | 20 (10.frontend/desugar, lib/common, database, env) | src/compiler/50.mir/_MirLowering/function_lowering.spl (Infer element type) | spec only (PR #5773, 2/2 seed): no infer-arm in reduced closure; full-closure only. revert-ready pending full stage3 build |
| typeparam-mir-20261031 | 19 (nogc_async_mut/io, 80.driver/cache) | static generic factory substitution (HIR/MIR, function_lowering.spl) | fixed-in-source (seed MIR probe clean; spec UNRUN; PR #5775). revert-ready for factory helpers; re-probe buffer.spl slice site first |
| rti004-mono-20261101 | 17 (driver_build, async_ring) | src/compiler/20.hir/return_type_interface_v1.spl x switch_operators_calls.spl | fixed-in-source (40.mono deleted 200a05f5bc8, no 2^50 ids; MIR repro UNRUN; status + design note PR #5778). revert-ready |
| ctor-mir-20261031 | 16 (80.driver/driver_build) | switch_operators_calls.spl, result_err_record_owner.spl | spec+design only (PR #5781, UNRUN): create() fixed; take() E-RTI-003, Ok(nil), [Fut<text>] field key, bare Some/None without import still fail. NOT revert-ready (only file_fiber_tldr_bridge_v1.spl:64 annotation) |
| mono-call-inference-20261031 | 13 (dbfs_driver, office/sheets, concurrent) | generic call inference (HIR/mono) | fixed-in-source (40.mono deleted 200a05f5bc8; seed probe clean; bug file + row PR #5780). revert-ready except channel_try_recv_by_id <i64> |
| ownerlayout-mir-20261031 | 12 (plugins/backend_lean, backend_vhdl, 80.driver, 50.mir) | MIR imported struct owner provenance | partial (PR #5774, 4/4 seed): SymbolId.name real-fixed; unwrap_err() field read with two CompileError owners still ambiguous (design: module-qualified owner key). NOT revert-ready |
| lambdaabi-mir-20261031 | 9 (nogc_async_mut/io, hir_lowering) | src/compiler/50.mir/_MirLoweringExpr/lambda_abi.spl, expr_dispatch.spl | fixed-in-source (seed MIR probe clean; spec UNRUN; PR #5779). revert-ready |
| stage2_ifexpr_continuation_else_parse_2026_11_01 | 3 (driver_build/incremental.spl, frontend spec, doc) | src/compiler/10.frontend expression parser | fixed (PR #5768, parser_stmts.spl; ifexpr_continuation_else_parse_spec 4/4 seed) |
| stage2_runtime_list_missing_process_tree_2026_11_01 | 3 (scripts/bootstrap/workarounds) | src/compiler/70.backend/backend/runtime_compiler.spl | fixed-in-source (runtime_compiler.spl :647/:739 lists runtime_process_tree; status PR #5770) |
| go_to_end_dynload_zero_objects_2026-11-01 | driver flag `--mode one-binary` (run scripts) | src/compiler/80.driver/driver_build/go_to_end.spl (go_to_end_emit_format_v1), driver_aot_pipeline.spl | fixed (PR #5766; seed spec 4/4; revert-ready after one phase-3 dynload go-to-end run shows objects) |

Bug files: `doc/08_tracking/bug/<id with _ and date>.md`. Rows exist in `bug_db.sdn` for
rti007_any_return_rows, rti004_mono, typeparam_mir, enumowner_mir, go_to_end_dynload,
stage2_runtime_list, stage2_ifexpr. mono-call-inference: doc/08_tracking/bug/mono_call_inference_2026-10-31.md (PR #5780). "seed" = Rust seed interpreting pure-Simple src/compiler in a reduced closure; UNRUN = written during the run-14c memory hold.
