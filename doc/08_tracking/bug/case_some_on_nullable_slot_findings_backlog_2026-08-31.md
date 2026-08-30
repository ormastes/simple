# `case Some(` on plain-nullable slots — classified sweep of src/compiler

Static analysis only. Nothing was edited, built, or bootstrapped.
Baseline: working tree at the commit after 6d3856e6b4b.

## Accounting: 497 grep hits

| | count |
|---|---|
| raw `/usr/bin/grep -rn "case Some(" src/compiler --include='*.spl'` | 497 |
| — of which COMMENT mentions, not code | 30 |
| **real code sites classified** | **467** |

The 30 comment hits are prose *about* this defect class. Several independently
document it (`20.hir/hir_lowering/_Expressions/expression_components.spl:223-224`,
`20.hir/hir_lowering/statements.spl:435`, `_Expressions/expression_support.spl:288`,
`50.mir/mir_lowering_stmts.spl:808,853`). That is corroboration of the premise from
prior investigators, not new evidence.

## Bucket counts (467 code sites)

| bucket | sites | basis |
|---|---|---|
| **B — DEFECTIVE (scrutinee declared plain `T?`)** | **218** | declaration lookup |
| A — SAFE (scrutinee declared `Option<T>`) | 31 | declaration lookup |
| C — ambiguous name (same name declared both `T?` and `Option<T>`) | 94 | unresolvable by name |
| C — no declaration found | 61 | key not in index |
| C — local var, binding unresolved | 53 | see Method risk 2 |
| C — scrutinee expression unparsed | 5 | |
| C — no enclosing `match` found | 5 | |
| **C total** | **218** | |

### B split by payload shape

| payload | sites | corruption mechanism |
|---|---|---|
| aggregate (struct/class/enum) | 111 | **(b) arm binding deep-copies → corrupts → SIGSEGV** |
| scalar (i64/bool/text/…) | 79 | (a) only; likely benign |
| type not determined | 28 | unknown |

### B by compiler layer

| layer | B sites |
|---|---|
| 80.driver | 46 |
| 70.backend | 40 |
| 50.mir | 36 |
| 35.semantics | 34 |
| 00.common | 17 |
| 99.loader | 16 |
| 60.mir_opt | 12 |
| 90.tools | 5 |
| 55.borrow | 5 |
| 95.interp | 2 |
| 30.types | 2 |
| 25.traits | 2 |
| 20.hir | 1 |

## Why declaration alone decides bucket B

A slot declared `T?` is bucket B **regardless of writer mix** — both writer
populations are broken, in different ways:

- `T?` + any `Some(...)` writer → the arm matches, and the Option-payload arm
  binding deep-copies the aggregate and corrupts it. This is mechanism (b),
  the SIGSEGV/`disc=-1` class proven by commit 6d3856e6b4b.
- `T?` + bare writers → the `Some` arm never matches the representation at all.
  Mechanism (a): **silent fallthrough**, no crash, wrong behaviour.

Only a slot declared `Option<T>` is genuinely safe (bucket A).

### Notable live finding — silent fallthrough in the safety checker

`safety_lookup_param`, `safety_lookup_iter` and `safety_transfer_lookup`
(`35.semantics/safety_checker*.spl`) are declared `-> SafetyParamTrack?` /
`SafetyIterTrack?` / `SafetyTransferBinding?` and return **bare** values
(`return pt`, `return it`, `return b`) — verified by reading each body. Every
reader tests them with `case Some(...)`, which therefore never matches. These
are not latent: the safety checks behind those arms are silently skipped today.

### Hot field slots are MIXED populations (hand-surveyed)

| field | `Some(` writers | bare writers |
|---|---|---|
| output_value | 1 | 2 |
| schema | 1 | 4 |
| payload | 4 | 74 |
| contract | 1 | 45 |
| init | 1 | 22 |
| type_ | 2 | 76 |
| resolved | 3 | 81 |

Every one is mixed — the exact shape the commit found for `HirSymbol.type_`
(13 of 56 `symbols.define(` sites box). The premise generalises.

## Declaration census (supports the premise)

| | `T?` | `Option<T>` |
|---|---|---|
| field declarations in src/compiler | 247 | 41 |
| fn return types in src/compiler | 554 | 43 |

The repo overwhelmingly declares plain nullables, so `case Some` is the
minority-correct idiom, not the default-correct one.

## Ranked bucket B — full table

Rank = hot path (0 = 20.hir/30.types/35.semantics/50.mir, 1 = 10.frontend/55.borrow/60.mir_opt/70.backend,
2 = rest), then aggregate before scalar.

| rank | site | slot/accessor | payload | binder | writers | declared type |
|---|---|---|---|---|---|---|
| 0.0 | src/compiler/20.hir/hir_lowering/_Expressions/block_and_asm_lowering.spl:182 | `output_value` | aggregate | named | MIXED (hand) | Expr,HirExpr |
| 0.0 | src/compiler/35.semantics/const_keys.spl:332 | `schema` | aggregate | named | MIXED (hand) | TemplateSchema |
| 0.0 | src/compiler/35.semantics/narrowing.spl:209 | `_extract_type_from_expr` | aggregate | named | all-Some | HirType |
| 0.0 | src/compiler/35.semantics/narrowing.spl:232 | `_extract_type_from_expr` | aggregate | named | all-Some | HirType |
| 0.0 | src/compiler/35.semantics/narrowing.spl:376 | `_negate_single_fact` | aggregate | named | all-Some | NarrowingFact |
| 0.0 | src/compiler/35.semantics/narrowing.spl:392 | `_unwrap_optional` | aggregate | named | unverified | HirType |
| 0.0 | src/compiler/35.semantics/safety_checker.spl:211 | `safety_lookup_param` | aggregate | named | all-bare | SafetyParamTrack |
| 0.0 | src/compiler/35.semantics/safety_checker.spl:223 | `safety_lookup_param` | aggregate | named | all-bare | SafetyParamTrack |
| 0.0 | src/compiler/35.semantics/safety_checker.spl:248 | `safety_lookup_param` | aggregate | named | all-bare | SafetyParamTrack |
| 0.0 | src/compiler/35.semantics/safety_checker.spl:290 | `safety_lookup_iter` | aggregate | named | all-bare | SafetyIterTrack |
| 0.0 | src/compiler/35.semantics/safety_checker.spl:300 | `safety_lookup_iter` | aggregate | named | all-bare | SafetyIterTrack |
| 0.0 | src/compiler/35.semantics/safety_checker.spl:336 | `safety_lookup_iter` | aggregate | named | all-bare | SafetyIterTrack |
| 0.0 | src/compiler/35.semantics/safety_checker_expr.spl:145 | `sffi_method_resolution_symbol` | aggregate | named | unverified | SymbolId |
| 0.0 | src/compiler/35.semantics/safety_checker_expr.spl:162 | `sffi_method_resolution_symbol` | aggregate | named | unverified | SymbolId |
| 0.0 | src/compiler/35.semantics/safety_checker_transfer.spl:168 | `safety_transfer_lookup` | aggregate | named | all-bare | SafetyTransferBinding |
| 0.0 | src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:261 | `init` | aggregate | named | field-survey | ComputeSessionError,GcComputeError,MirConstant |
| 0.0 | src/compiler/50.mir/_MirLowering/function_lowering.spl:1322 | `output_value` | aggregate | named | MIXED (hand) | Expr,HirExpr |
| 0.0 | src/compiler/50.mir/_MirLowering/module_lowering.spl:420 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/_MirLowering/module_lowering.spl:437 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4295 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2579 | `type_` | aggregate | named | field-survey | HirType |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2833 | `lookup_method_in_type` | aggregate | named | unverified | SymbolId |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2835 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2882 | `lookup_method_in_type` | aggregate | named | unverified | SymbolId |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2884 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2948 | `lookup_method_in_type` | aggregate | named | unverified | SymbolId |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2950 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:364 | `find_local_hir_type` | aggregate | named | all-Some | HirType |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:375 | `find_local_hir_type` | aggregate | named | all-Some | HirType |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:728 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2565 | `get_symbol_raw` | aggregate | named | all-bare | HirSymbol |
| 0.0 | src/compiler/50.mir/mir_data.spl:253 | `current_function` | aggregate | named | field-survey | MirFunction,SymbolId,text |
| 0.0 | src/compiler/50.mir/mir_lowering_stmts.spl:1142 | `get_symbol_type_raw` | aggregate | named | unverified | HirType |
| 0.0 | src/compiler/50.mir/mir_lowering_stmts.spl:1593 | `find_local_hir_type` | aggregate | named | all-Some | HirType |
| 0.0 | src/compiler/50.mir/mir_lowering_stmts.spl:1647 | `find_local_hir_type` | aggregate | named | all-Some | HirType |
| 0.0 | src/compiler/50.mir/mir_lowering_stmts.spl:2949 | `type_` | aggregate | named | field-survey | HirType |
| 0.0 | src/compiler/50.mir/mir_lowering_stmts.spl:2955 | `type_` | aggregate | named | field-survey | HirType |
| 0.0 | src/compiler/50.mir/mir_lowering_stmts.spl:3104 | `type_` | aggregate | named | field-survey | HirType |
| 0.0 | src/compiler/50.mir/verification_contract_bridge.spl:497 | `contract` | aggregate | named | field-survey | VerificationFunctionContractV1 |
| 0.0 | src/compiler/50.mir/verification_contract_bridge.spl:579 | `contract` | aggregate | named | field-survey | VerificationFunctionContractV1 |
| 0.0 | src/compiler/50.mir/verification_contract_bridge.spl:786 | `verification_contract` | aggregate | named | field-survey | HirContractBlock,HirContractBlock |
| 0.0 | src/compiler/50.mir/verification_obligation_closure.spl:584 | `contract` | aggregate | named | field-survey | VerificationFunctionContractV1 |
| 0.0 | src/compiler/50.mir/verification_obligation_module.spl:138 | `contract` | aggregate | named | field-survey | VerificationFunctionContractV1 |
| 0.0 | src/compiler/50.mir/verification_obligation_module.spl:194 | `contract` | aggregate | named | field-survey | VerificationFunctionContractV1 |
| 0.1 | src/compiler/35.semantics/aspect_seal/facet_model.spl:241 | `facet_activation_from_text` | ? | named | unknown |  |
| 0.1 | src/compiler/35.semantics/aspect_seal/facet_model.spl:359 | `as_array` | ? | named | unverified |  |
| 0.1 | src/compiler/35.semantics/aspect_seal/facet_model.spl:375 | `as_array` | ? | named | unverified |  |
| 0.1 | src/compiler/35.semantics/aspect_seal/facet_model.spl:395 | `as_array` | ? | named | unverified |  |
| 0.1 | src/compiler/35.semantics/aspect_seal/facet_model.spl:433 | `as_array` | ? | named | unverified |  |
| 0.1 | src/compiler/35.semantics/narrowing.spl:230 | `type_lookup` | ? | named | unknown |  |
| 0.1 | src/compiler/35.semantics/narrowing.spl:253 | `type_lookup` | ? | named | unknown |  |
| 0.1 | src/compiler/35.semantics/narrowing.spl:273 | `type_lookup` | ? | named | unknown |  |
| 0.1 | src/compiler/35.semantics/narrowing.spl:297 | `type_lookup` | ? | named | unknown |  |
| 0.1 | src/compiler/35.semantics/resolve.spl:273 | `get_type_symbol` | ? | named | unknown |  |
| 0.1 | src/compiler/35.semantics/resolve.spl:289 | `get_type_symbol` | ? | named | unknown |  |
| 0.1 | src/compiler/50.mir/verification_call_identity.spl:200 | `resolved_direct_call_binding_for_site_v1` | ? | named | unverified |  |
| 0.1 | src/compiler/50.mir/verification_call_manifest_finalizer.spl:93 | `finalizer_function_by_symbol_v1` | ? | named | unverified |  |
| 0.1 | src/compiler/50.mir/verification_ir.spl:707 | `effects_for` | ? | named | all-Some |  |
| 0.1 | src/compiler/50.mir/verification_obligation_closure.spl:333 | `proof_discharge_for_obligation_v1` | ? | named | unverified |  |
| 0.1 | src/compiler/50.mir/verification_obligation_closure.spl:378 | `proof_discharge_for_obligation_v1` | ? | named | unverified |  |
| 0.1 | src/compiler/50.mir/verification_obligation_closure.spl:392 | `proof_discharge_for_obligation_v1` | ? | named | unverified |  |
| 0.2 | src/compiler/30.types/dim_constraints.spl:140 | `try_eval` | scalar | named | unverified | i64 |
| 0.2 | src/compiler/30.types/dim_constraints.spl:142 | `try_eval` | scalar | named | unverified | i64 |
| 0.2 | src/compiler/35.semantics/aspect_seal/facet_model.spl:326 | `_text_at` | scalar | named | unverified | text,text,text |
| 0.2 | src/compiler/35.semantics/aspect_seal/facet_model.spl:333 | `_text_at` | scalar | named | unverified | text,text,text |
| 0.2 | src/compiler/35.semantics/aspect_seal/facet_model.spl:341 | `as_bool` | scalar | named | unverified | bool,bool,bool,bool,bool |
| 0.2 | src/compiler/35.semantics/aspect_seal/facet_model.spl:349 | `as_i64` | scalar | named | unverified | i64,i64 |
| 0.2 | src/compiler/35.semantics/aspect_seal/facet_model.spl:362 | `as_str` | scalar | named | unverified | text,text |
| 0.2 | src/compiler/35.semantics/error_formatter.spl:155 | `get_type_mismatch_hint` | scalar | named | unverified | text |
| 0.2 | src/compiler/35.semantics/error_formatter.spl:346 | `file` | scalar | named | field-survey | text,text,text |
| 0.2 | src/compiler/35.semantics/simd_check.spl:401 | `iteration_count` | scalar | named | field-survey | i64,i64 |
| 0.2 | src/compiler/35.semantics/visibility_integration.spl:184 | `defining_module` | scalar | named | field-survey | text |
| 0.2 | src/compiler/50.mir/_MirLowering/module_lowering.spl:449 | `defining_module` | scalar | named | field-survey | text |
| 1.0 | src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl:279 | `rewrite_single_use_len_consumer` | aggregate | named | all-Some | MirInst |
| 1.0 | src/compiler/60.mir_opt/mir_opt/outline.spl:474 | `find_group_exit` | aggregate | named | all-Some | BlockId |
| 1.0 | src/compiler/70.backend/backend/cuda_backend.spl:1538 | `payload` | aggregate | named | field-survey | MirType,text |
| 1.0 | src/compiler/70.backend/backend/cuda_backend.spl:1549 | `payload` | aggregate | named | field-survey | MirType,text |
| 1.0 | src/compiler/70.backend/backend/vhdl/vhdl_call_lowering.spl:726 | `direct_hardware_callee` | aggregate | named | unverified | MirFunction |
| 1.0 | src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl:317 | `payload` | aggregate | named | field-survey | MirType,text |
| 1.0 | src/compiler/70.backend/backend/vhdl/vhdl_design_catalog.spl:338 | `init` | aggregate | named | field-survey | ComputeSessionError,GcComputeError,MirConstant |
| 1.0 | src/compiler/70.backend/backend/vhdl_expr.spl:100 | `unsupported_type_error` | aggregate | named | unverified | CompileError |
| 1.0 | src/compiler/70.backend/backend/vhdl_expr.spl:368 | `payload` | aggregate | named | field-survey | MirType,text |
| 1.0 | src/compiler/70.backend/backend/vhdl_expr.spl:474 | `unsupported_type_error` | aggregate | named | unverified | CompileError |
| 1.0 | src/compiler/70.backend/backend/vhdl_validation.spl:251 | `payload` | aggregate | named | field-survey | MirType,text |
| 1.0 | src/compiler/70.backend/backend/vhdl_validation.spl:267 | `unsupported_type_error` | aggregate | named | unverified | CompileError |
| 1.0 | src/compiler/70.backend/backend/vhdl_validation.spl:289 | `unsupported_type_error` | aggregate | named | unverified | CompileError |
| 1.0 | src/compiler/70.backend/backend/vhdl_validation.spl:690 | `payload` | aggregate | named | field-survey | MirType,text |
| 1.0 | src/compiler/70.backend/backend/vhdl_validation.spl:735 | `payload` | aggregate | named | field-survey | MirType,text |
| 1.0 | src/compiler/70.backend/lowering/intrinsic_lowering_aarch64.spl:154 | `intrinsic_to_target_idiom_aarch64` | aggregate | named | unverified | TargetIdiom |
| 1.0 | src/compiler/70.backend/lowering/intrinsic_lowering_riscv.spl:141 | `intrinsic_to_target_idiom_riscv` | aggregate | named | unverified | TargetIdiom |
| 1.0 | src/compiler/70.backend/lowering/intrinsic_lowering_x86.spl:251 | `intrinsic_to_target_idiom` | aggregate | named | unverified | TargetIdiom |
| 1.2 | src/compiler/55.borrow/gc_analysis/mod.spl:215 | `operand_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/55.borrow/gc_analysis/mod.spl:217 | `operand_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/55.borrow/gc_analysis/mod.spl:239 | `operand_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/55.borrow/gc_analysis/mod.spl:259 | `operand_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/55.borrow/gc_analysis/mod.spl:276 | `operand_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/_OptimizationPasses/io_passes.spl:548 | `primitive_size` | scalar | named | unverified | i64,i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/_Inline/driver.spl:378 | `extract_func_symbol_id` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/collection_opt_patterns.spl:402 | `colopt_operand_to_local_id` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/collection_opt_patterns.spl:404 | `colopt_operand_to_local_id` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/collection_opt_patterns.spl:428 | `colopt_operand_to_local_id` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/mod.spl:1343 | `mir_pass_backend_skip_reason_fast` | scalar | wildcard | all-Some | text |
| 1.2 | src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl:229 | `var_reassign_written_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl:249 | `var_reassign_written_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/var_reassign_analysis.spl:99 | `var_reassign_operand_local` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl:1001 | `ssa_phi_plan_pred_value_for_block` | scalar | named | all-Some | i64 |
| 1.2 | src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl:176 | `reset_signal` | scalar | named | field-survey | text |
| 1.2 | src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl:571 | `reset_signal` | scalar | named | field-survey | text |
| 1.2 | src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl:588 | `reset_signal` | scalar | named | field-survey | text |
| 1.2 | src/compiler/70.backend/backend/backend_types.spl:404 | `location` | scalar | named | field-survey | text,text |
| 1.2 | src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:785 | `cranelift_phi_const_block_arg` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/cranelift_gemm_fusion.spl:29 | `operand_copy_local_id` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/llvm_backend_tools.spl:210 | `abi` | scalar | named | field-survey | text |
| 1.2 | src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:726 | `ssa_phi_const_block_arg` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/llvm_lib_translate_expr.spl:728 | `ssa_phi_const_block_arg` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/native/isel_riscv64.spl:405 | `label` | scalar | named | field-survey | text |
| 1.2 | src/compiler/70.backend/backend/vhdl/vhdl_abi.spl:59 | `vhdl_data_width_bits` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:37 | `fixed_width_diagnostic` | scalar | named | unverified | text |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:480 | `integer_width` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:560 | `integer_width` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:592 | `integer_width` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:66 | `integer_width` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:72 | `integer_width` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:78 | `integer_width` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_expr.spl:80 | `integer_width` | scalar | named | unverified | i64 |
| 1.2 | src/compiler/70.backend/backend/vhdl_validation.spl:34 | `unsupported_mir_type_diagnostic` | scalar | named | unverified | text |
| 1.2 | src/compiler/70.backend/linker/msvc.spl:123 | `find_link_exe` | scalar | named | all-Some | text |
| 1.2 | src/compiler/70.backend/linker/msvc.spl:211 | `find_visual_studio` | scalar | named | unverified | text |
| 1.2 | src/compiler/70.backend/linker/msvc.spl:246 | `find_visual_studio` | scalar | named | unverified | text |
| 1.2 | src/compiler/70.backend/linker/msvc.spl:281 | `find_link_exe` | scalar | wildcard | all-Some | text |
| 2.0 | src/compiler/00.common/assurance/package_pins.spl:486 | `_pin_find_by_name` | aggregate | named | all-Some | PackagePin |
| 2.0 | src/compiler/00.common/assurance/package_pins.spl:490 | `_find_by_dir` | aggregate | named | all-Some | PackagePin |
| 2.0 | src/compiler/00.common/assurance/package_pins.spl:513 | `_pin_find_by_name` | aggregate | named | all-Some | PackagePin |
| 2.0 | src/compiler/00.common/assurance/package_pins.spl:573 | `_pin_find_by_name` | aggregate | named | all-Some | PackagePin |
| 2.0 | src/compiler/00.common/assurance/package_pins.spl:631 | `_pin_find_by_name` | aggregate | named | all-Some | PackagePin |
| 2.0 | src/compiler/00.common/dependency/visibility.spl:320 | `symbol_visibility` | aggregate | named | all-Some | Visibility,Visibility,Visibility |
| 2.0 | src/compiler/00.common/dependency/visibility.spl:323 | `symbol_visibility` | aggregate | named | all-Some | Visibility,Visibility,Visibility |
| 2.0 | src/compiler/00.common/dependency/visibility.spl:325 | `symbol_visibility` | aggregate | named | all-Some | Visibility,Visibility,Visibility |
| 2.0 | src/compiler/00.common/dependency/visibility.spl:327 | `symbol_visibility` | aggregate | named | all-Some | Visibility,Visibility,Visibility |
| 2.0 | src/compiler/00.common/dependency/visibility.spl:329 | `symbol_visibility` | aggregate | named | all-Some | Visibility,Visibility,Visibility |
| 2.0 | src/compiler/00.common/dependency/visibility.spl:331 | `symbol_visibility` | aggregate | named | all-Some | Visibility,Visibility,Visibility |
| 2.0 | src/compiler/25.traits/trait_solver.spl:249 | `find_impl` | aggregate | named | MIXED | ImplBlock |
| 2.0 | src/compiler/25.traits/trait_solver.spl:360 | `find_impl` | aggregate | named | MIXED | ImplBlock |
| 2.0 | src/compiler/80.driver/cache/cas_store.spl:251 | `action_manifest_parse` | aggregate | named | unverified | ActionManifest |
| 2.0 | src/compiler/80.driver/cache/cas_store.spl:344 | `result_manifest_parse` | aggregate | named | unverified | ResultManifest |
| 2.0 | src/compiler/80.driver/cache/gc/mark_sweep.spl:163 | `action_manifest_parse` | aggregate | named | unverified | ActionManifest |
| 2.0 | src/compiler/80.driver/cache/lease/lease.spl:147 | `lease_parse` | aggregate | named | unverified | CacheLease |
| 2.0 | src/compiler/80.driver/cache/lease/lease.spl:192 | `lease_parse` | aggregate | named | unverified | CacheLease |
| 2.0 | src/compiler/80.driver/cache/lease/lease.spl:214 | `lease_parse` | aggregate | named | unverified | CacheLease |
| 2.0 | src/compiler/80.driver/cache/remote/remote_client.spl:107 | `fetch_result_manifest` | aggregate | named | unverified | RemoteResultManifest |
| 2.0 | src/compiler/80.driver/cache/remote/remote_client.spl:123 | `fetch_artifact` | aggregate | named | unverified | RemoteArtifact |
| 2.0 | src/compiler/80.driver/cache/remote/remote_client.spl:93 | `fetch_action_mapping` | aggregate | named | unverified | RemoteActionMapping |
| 2.0 | src/compiler/80.driver/cache/tier_router/tier_router.spl:127 | `result_manifest_get` | aggregate | named | all-bare | ResultManifest |
| 2.0 | src/compiler/80.driver/cache/tier_router/tier_router.spl:140 | `result_manifest_get` | aggregate | named | all-bare | ResultManifest |
| 2.0 | src/compiler/80.driver/driver_bootstrap.spl:161 | `bootstrap_entry_hir` | aggregate | named | field-survey | HirModule |
| 2.0 | src/compiler/80.driver/driver_source_loading.spl:1328 | `span` | aggregate | named | field-survey | SourceSpan,Span,Span,Span,Span,Span,Span,Span,Span,Span,Span,Span,Span |
| 2.0 | src/compiler/80.driver/hydration_manifest.spl:103 | `options` | aggregate | named | field-survey | EventOptions |
| 2.0 | src/compiler/80.driver/hydration_manifest.spl:111 | `metadata` | aggregate | named | field-survey | ManifestMetadata,MonomorphizationMetadata |
| 2.0 | src/compiler/80.driver/hydration_manifest.spl:145 | `options` | aggregate | named | field-survey | EventOptions |
| 2.0 | src/compiler/80.driver/hydration_manifest.spl:93 | `options` | aggregate | named | field-survey | EventOptions |
| 2.0 | src/compiler/80.driver/hydration_manifest.spl:98 | `options` | aggregate | named | field-survey | EventOptions |
| 2.0 | src/compiler/80.driver/main.spl:340 | `next` | aggregate | named | all-bare | EntityState,Item,Self.Item,Self.Item,i64 |
| 2.0 | src/compiler/80.driver/project.spl:213 | `get_path` | aggregate | named | all-bare | SdnValue |
| 2.0 | src/compiler/80.driver/project.spl:215 | `as_dict` | aggregate | named | unverified | Dict<text,SdnValue> |
| 2.0 | src/compiler/80.driver/project.spl:39 | `get_path` | aggregate | named | all-bare | SdnValue |
| 2.0 | src/compiler/80.driver/project.spl:61 | `get_path` | aggregate | named | all-bare | SdnValue |
| 2.0 | src/compiler/80.driver/project.spl:78 | `get_path` | aggregate | named | all-bare | SdnValue |
| 2.0 | src/compiler/80.driver/smf_writer.spl:239 | `templates` | aggregate | named | field-survey | GenericTemplates |
| 2.0 | src/compiler/80.driver/smf_writer.spl:245 | `metadata` | aggregate | named | field-survey | ManifestMetadata,MonomorphizationMetadata |
| 2.0 | src/compiler/80.driver/smf_writer.spl:251 | `note_sdn` | aggregate | named | field-survey | NoteSdnMetadata,NoteSdnMetadata |
| 2.0 | src/compiler/80.driver/watcher/smf_manifest.spl:237 | `parse_manifest_entry_line` | aggregate | named | unverified | SmfManifestEntry |
| 2.0 | src/compiler/80.driver/watcher/watcher_daemon.spl:193 | `smf_manifest_find` | aggregate | named | all-Some | SmfManifestEntry |
| 2.0 | src/compiler/90.tools/fix/rules/impl_/lint_code.spl:173 | `_parse_duplicate_typed_arg_signature` | aggregate | named | unverified | DuplicateTypedArgSignature,DuplicateTypedArgSignature |
| 2.0 | src/compiler/90.tools/sffi_audit/hir_inventory.spl:102 | `sffi_method_resolution_symbol` | aggregate | named | unverified | SymbolId |
| 2.0 | src/compiler/90.tools/sffi_audit/hir_inventory.spl:110 | `sffi_method_resolution_symbol` | aggregate | named | unverified | SymbolId |
| 2.0 | src/compiler/99.loader/completeness_seal/manifest.spl:143 | `as_dict` | aggregate | named | unverified | Dict<text,SdnValue> |
| 2.0 | src/compiler/99.loader/completeness_seal/manifest.spl:223 | `as_dict` | aggregate | named | unverified | Dict<text,SdnValue> |
| 2.0 | src/compiler/99.loader/settlement/builder.spl:142 | `get_export` | aggregate | named | unverified | SymbolEntry |
| 2.0 | src/compiler/99.loader/settlement/builder.spl:154 | `get_module` | aggregate | named | MIXED | LoadedModule,ModuleEntry |
| 2.1 | src/compiler/00.common/assurance/package_pins.spl:323 | `as_array` | ? | named | unverified |  |
| 2.1 | src/compiler/00.common/assurance/package_pins.spl:350 | `as_array` | ? | named | unverified |  |
| 2.1 | src/compiler/00.common/assurance/package_pins.spl:430 | `as_array` | ? | named | unverified |  |
| 2.1 | src/compiler/80.driver/project.spl:80 | `as_array` | ? | named | unverified |  |
| 2.1 | src/compiler/90.tools/formatter/main.spl:404 | `index_of` | ? | named | all-bare |  |
| 2.1 | src/compiler/90.tools/formatter/main.spl:461 | `index_of` | ? | named | all-bare |  |
| 2.1 | src/compiler/99.loader/completeness_seal/admission.spl:179 | `closure_from_text` | ? | named | unknown |  |
| 2.1 | src/compiler/99.loader/completeness_seal/manifest.spl:271 | `as_array` | ? | named | unverified |  |
| 2.1 | src/compiler/99.loader/completeness_seal/manifest.spl:321 | `as_array` | ? | named | unverified |  |
| 2.1 | src/compiler/99.loader/completeness_seal/seal.spl:240 | `closure_from_text` | ? | named | unknown |  |
| 2.1 | src/compiler/99.loader/completeness_seal/seal.spl:253 | `closure_from_text` | ? | named | unknown |  |
| 2.2 | src/compiler/00.common/assurance/package_pins.spl:262 | `_text_at` | scalar | named | unverified | text,text,text |
| 2.2 | src/compiler/00.common/assurance/package_pins.spl:270 | `as_bool` | scalar | named | unverified | bool,bool,bool,bool,bool |
| 2.2 | src/compiler/00.common/assurance/package_pins.spl:283 | `as_str` | scalar | named | unverified | text,text |
| 2.2 | src/compiler/80.driver/cache/action_index/action_index.spl:101 | `action_index_read_raw` | scalar | named | all-bare | text |
| 2.2 | src/compiler/80.driver/cache/action_index/action_index.spl:113 | `action_index_read_raw` | scalar | named | all-bare | text |
| 2.2 | src/compiler/80.driver/cache/action_index/action_index.spl:132 | `action_index_read_raw` | scalar | named | all-bare | text |
| 2.2 | src/compiler/80.driver/cache/gc/admission.spl:63 | `admission_file_size_raw` | scalar | named | unverified | usize |
| 2.2 | src/compiler/80.driver/cache/gc/admission.spl:98 | `admission_file_size_raw` | scalar | named | unverified | usize |
| 2.2 | src/compiler/80.driver/cache/gc/fast_gc.spl:100 | `gc_file_size_raw` | scalar | named | unverified | usize |
| 2.2 | src/compiler/80.driver/cache/gc/fast_gc.spl:208 | `gc_file_size_raw` | scalar | named | unverified | usize |
| 2.2 | src/compiler/80.driver/cache/integration/shadow_mode.spl:138 | `cas_get` | scalar | named | unverified | text |
| 2.2 | src/compiler/80.driver/cache/tier_router/tier_router.spl:99 | `cas_get` | scalar | named | unverified | text |
| 2.2 | src/compiler/80.driver/driver_bootstrap.spl:44 | `opt_level` | scalar | named | field-survey | i64,i64 |
| 2.2 | src/compiler/80.driver/driver_source_loading.spl:1333 | `help` | scalar | named | field-survey | text,text,text |
| 2.2 | src/compiler/80.driver/hydration_manifest.spl:117 | `wasm_size` | scalar | named | field-survey | i64 |
| 2.2 | src/compiler/80.driver/project.spl:41 | `as_str` | scalar | named | unverified | text,text |
| 2.2 | src/compiler/80.driver/project.spl:44 | `as_i64` | scalar | named | unverified | i64,i64 |
| 2.2 | src/compiler/80.driver/project.spl:47 | `as_bool` | scalar | named | unverified | bool,bool,bool,bool,bool |
| 2.2 | src/compiler/80.driver/project.spl:63 | `as_bool` | scalar | named | unverified | bool,bool,bool,bool,bool |
| 2.2 | src/compiler/95.interp/mir_interpreter.spl:1071 | `current_block` | scalar | named | field-survey | i64,i64 |
| 2.2 | src/compiler/95.interp/mir_interpreter.spl:1149 | `previous_block` | scalar | named | field-survey | i64,i64 |
| 2.2 | src/compiler/99.loader/completeness_seal/manifest.spl:107 | `_text_at` | scalar | named | unverified | text,text,text |
| 2.2 | src/compiler/99.loader/completeness_seal/manifest.spl:126 | `as_i64` | scalar | named | unverified | i64,i64 |
| 2.2 | src/compiler/99.loader/completeness_seal/manifest.spl:153 | `_text_at` | scalar | named | unverified | text,text,text |
| 2.2 | src/compiler/99.loader/completeness_seal/manifest.spl:226 | `as_str` | scalar | named | unverified | text,text |
| 2.2 | src/compiler/99.loader/completeness_seal/manifest.spl:293 | `as_i64` | scalar | named | unverified | i64,i64 |
| 2.2 | src/compiler/99.loader/completeness_seal/manifest.spl:324 | `as_str` | scalar | named | unverified | text,text |
| 2.2 | src/compiler/99.loader/completeness_seal/manifest.spl:46 | `handler_for` | scalar | wildcard | all-Some | text,text |

## Calibration against the one ground-truth slot

`HirSymbol.type_` is the only slot with an independently PROVEN classification
(commit 6d3856e6b4b: mixed, 13 of 56 `symbols.define(` sites box). The method
files it in **bucket B**, correctly and unambiguously — every `type_` declaration
in the index is a plain `T?`, so the ambiguity rule never fires on it. That is a
validation win for the declaration-based rule.

It also shows the sweep is finding real, UNFIXED work: the commit fixed two sites,
and four more `case Some` readers of this same proven-mixed slot remain:

- `src/compiler/50.mir/mir_lowering_stmts.spl:2949`
- `src/compiler/50.mir/mir_lowering_stmts.spl:2955`
- `src/compiler/50.mir/mir_lowering_stmts.spl:3104`
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2579`

Caveat in the other direction: because ambiguous names are demoted wholesale,
bucket C certainly contains further known-B members. C is "unclassified", not "safe".

## Method, and where it is weak

1. **Extraction.** For each `case Some(` line, the enclosing `match <expr>:` is
   found by an indent-scoped stack (entries at indent >= the current line are
   dropped before each line, so a `match` from an earlier function cannot leak).
   467/467 code sites attributed; 5 had no enclosing `match` and are in C.
2. **LOCAL resolution is the weakest link, and was demoted rather than trusted.**
   Bare-identifier scrutinees were resolved to their nearest preceding
   `val`/`var` binding. A hand spot-check of 10 such sites found 6 correctly
   same-function and 4 where **no binding exists at all** (fn params, or
   assigned via a form the scan misses). For those the classifier would have
   fallen back to matching a *local variable name* against a global field/fn
   index — unsound. All 53 such rows were therefore moved to
   `C-local-unresolved`. This is why bucket B fell from 278 to 218.
3. **Name-based declaration lookup.** Field/fn keys are matched by name against
   an index built from src/compiler + src/lib. A name declared *only* as `T?`
   is sound regardless of how many classes declare it (whichever one it is, it
   is a plain nullable). A name declared both ways is `C-ambiguous-name` (94),
   not A and not B.
4. **Writer survey refines ranking only, never bucket membership.** Symptom
   class comes from an indent-scoped scan of `return` statements. 46 fns showed
   only `nil`/`None` explicit returns — Simple allows implicit trailing-expression
   returns and single-line bodies, which that scan does not see, so those are
   marked `unverified` inside B rather than promoted or demoted.
5. **Not done:** no per-field writer survey beyond the 7 hot keys hand-checked
   above; `C-nodecl` (61) was not chased into src/app or the runtime.

## Premise corrections

None to the premise itself. The declaration census, the seven mixed hot fields,
and the three all-bare safety-checker accessors all support it.

The corrections are to *scope*: the defect is repo-wide, not 50.mir-local
(50.mir is 36 of 218 B sites; 80.driver at 46 and 70.backend at 40 are larger),
and 218 of 467 sites could not be classified either way — bucket C is as large
as bucket B, so this sweep bounds the problem, it does not close it.
