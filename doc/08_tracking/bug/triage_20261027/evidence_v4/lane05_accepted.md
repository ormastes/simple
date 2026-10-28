# V4 lane 05 accepted evidence

Accepted classifications in V4: 158. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 129 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 05 evidence](../evidence_v3/lane05_accepted.md).

- 29 additional accepted records are detailed below.

## native_isel_and_c_backend_tuple_field_type_reconciliation_gap_2026-08-08 — Native isel lanes mis-reconcile float tuple/struct field types (register-class gap)

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_isel_and_c_backend_tuple_field_type_reconciliation_gap_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/native/isel_x86_64.spl:1077-1093; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/native/regalloc.spl:311-333; reviews/research_v2_12.md#native_isel_and_c_backend_tuple_field_type_reconciliation_gap_2026-08-08; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/native/isel_x86_64.spl:340-382,670-739,840-878,1077-1093; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/native/regalloc.spl:311-333; history 88aac2ffe28 deletion of _CBackendTranslate/instruction_lowering.spl
```
- Review rationale: The report correctly separates raw pointer bits from floating-point value semantics. Target x86 GetField still emits a generic word load and ordinary scalar BinOp emits ADD/IMUL/IDIV without a floating operand type. New SIMD allocation is a separate explicit Vec8f load/binop path with width/admission constraints, so XMM/YMM availability does not by itself repair scalar fields. History identifies the 794-line C translator deletion in the release-tree transplant; it does not prove an equivalent successor or preserve the historical C fix. Accept the real historical/current scalar-gap concern, with unknown full cross-backend remedy and no broad zero-SIMD or C-fixed assertion. Other native lanes and a C successor/retirement decision remain outside any admitted repair claim.
- Review corrections: Reconciled SIMD versus scalar paths and identified actual C deletion history. Withdraw the obsolete universal no-float-register wording and current C-fixed assertion without treating deletion as invalidity.

## native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19 — Native MIR for llm_caret cs_main: 21 lambdas hit E-MIR-EXPR-Lambda (closure conversion not run), enum == lowered as missing struct __eq__, unresolved close/is_open

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
input/open_bugs_05.tsv#native_mir_lambda_and_enum_eq_block_caret_cs_2026_10_19; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:7055-7076; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2202-2217; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/io/buffer.spl:215-229; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/io/buffer.spl:134-165,215-229; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:7576-7698; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4511-4546; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2202-2217
```
- Review rationale: The retained description gives concrete old cs_main diagnostics, but target buffer read now binds a typed Future before then and captures self/size in a lambda. Actual lambda lifting synthesizes a separate MIR function/environment and rejects unsupported capture scans, unresolved captures, F32 captures and some ABI combinations; the remaining error text does not show conversion never ran. Enum equality has owner-sensitive routing ahead of struct dunders, and close/is_open now use an optional AsyncClose field with trait dispatch. Those distinct mechanisms explain why the historical three-family diagnostic bundle cannot be assigned one known current fix. Accept valid/unknown/current-untested; exact owner metadata for the five reported enum types and all twenty-one call-site capture/admission records would be needed to claim full repair.
- Review corrections: Rejected closure-conversion-absent and aggregate-fixed conclusions. Examined an actual buffer capture and current lambda/enum dispatch bodies; retained unknown aggregate remedy rather than guessing from the diagnostic string.

## native_trait_typed_return_receiver_unresolved_2026-08-09 — native-build MIR lowering fails when a trait-typed return value is used as a method rece

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_trait_typed_return_receiver_unresolved_2026-08-09.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2202-2217; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:790-807; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/native_trait_conversion.spl:223-268; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/02_requirements/language/type_system/native_trait_object_dispatch_options.md:11-30; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/native_trait_receiver_resolution/main.spl:21-39,59-73; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2591-2611; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/native_trait_registration.spl:9-12,73-90; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:794-806; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:2574-2643; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/native_trait_conversion.spl:29-110; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/native_trait_calls.spl:16-31,82-93; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/04_smoke/native_trait_two_owner_dispatch.spl:41-70
```
- Review rationale: The preserved make_greeter().greet fixture is live. The old no-vtable/no-trait-index policy premise is superseded in implementation: module lowering registers trait declarations and implementations; return lowering coerces a concrete FriendlyGreeter result into the declared trait object; call-expression type recovery reads the function return type; method lowering chooses the native trait owner before legacy concrete-name lookup; the slot call uses registered object-safe methods and retains result type. This is the concrete structural remedy to the original Greeter-versus-FriendlyGreeter symbol-key mismatch, not a guessed single-impl shortcut. The two-owner smoke checks distinct returned implementations, mutation and optional fields. Source remedy is present, but no qualified execution was performed; recommend fixed_pending_verification, not closure or policy approval.
- Review corrections: Changed unknown/unknown/keep_open to known/yes/fixed_pending_verification after tracing registration, return conversion, call receiver type recovery and dynamic slot dispatch. Old policy absence is stale; smoke source is not a runtime PASS.

## no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09 — check-bootstrap-essential-tools-smoke.shs fails on a clean tree with error=rust_seed_bin

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09.md:195-217; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-bootstrap-essential-tools-smoke.shs:27-67,126-135; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09.md:195-217
```
- Review rationale: Historical Linux and Windows deployment identities document a genuine missing admitted CLI prerequisite. The target gate checks executable presence, bounds version probing, rejects Rust seed banners, and then requires real test-runner pass/failure behavior; retaining that guard is correct. Neither source inspection nor the old Windows digest is an October deployment receipt, so this classification makes no assertion that the currently deployed artifact is absent or qualified. The blocker remains historically valid, current-untested, with no diagnosed bootstrap/build remedy. A digest-bound Stage4 admission and full-CLI receipt is needed for a later fixed claim, not to classify the documented prerequisite failure conservatively.
- Review corrections: Accepted the historical-valid/current-untested classification with explicit deployment-identity boundary. Removed any implication that a present receipt was inspected or that the correct guard makes the issue invalid.

## option_predicate_returns_payload_not_bool_2026-07-28 — `.?` on Option returns the payload object, not bool — both engines

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/option_predicate_returns_payload_not_bool_2026-07-28.md:11-50; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_AstExpr/nodes.spl:66; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval.spl:485-493; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:75-117,793-824,872-899; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/30.types/bidirectional_checking.spl:329-347; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/option_predicate_returns_payload_not_bool_2026-07-28.md:11-38
```
- Review rationale: Split the actual claims. Present-or-nil .? is the documented compiler behavior, so strict bool expectations alone cannot establish an operator bug. The report separately records a declared bool function returning UnitEntry. The inspected seed result path extracts explicit/tail values and its contract validator rejects missing/nil results and validates unit types, but returns other nonnil values unchanged; it does not enforce a bool value there. A general return-checking test exists in the type subsystem, but does not establish this interpreter execution route or a bool-object regression. Preserve validity for the concrete return-contract symptom, unknown cross-engine root remedy, and current untested status. No proposal to change .? semantics or normalize arbitrary objects to booleans is admitted.
- Review corrections: Changed uncertain to valid for the independently stated bool-return mismatch, supported by the actual return boundary. The operator-is-bool premise remains rejected; no universal cross-engine invalid closure.

## optional_query_operator_identity_passthrough_2026-07-20 — Interpreter: `.?` operator is an identity pass-through, not a bool conversion

- Source receipt: `first_half_final_triage`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/optional_query_operator_identity_passthrough_2026-07-20.md:256-289; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/optional_query_operator_identity_passthrough_2026-07-20.md:15-20,220-289; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_AstExpr/nodes.spl:66; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval.spl:485-493; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/eval_access.spl:471-483; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter/expr.rs:415-492; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:819; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/database/sql/types.spl:131-139; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/shared/types/try_operator_nil_none_spec.spl:10-21; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/shared/types/try_operator_nil_none_class_spec.spl:23-97; history a74715af3e7d82db5b5200dc6b9054f9474fbdc3
```
- Review rationale: This mixed record cannot be closed invalid: September correctly rejects strict true/false pins for .?, while lines 220-242 describe the separate real DbRow.get(column)? bare-nil failure. The SQL getter still returns nil for absent columns. Target Rust Expr::Try explicitly converts Value::Nil to TryError(Nil), and function execution catches that propagation; the pure-Simple evaluator has the matching early-return path. Ancestor a74715af3e7 adds exactly the missing Nil arm, and current dedicated regressions assert nil direct, after Some and nested propagation plus Some/Ok/Err positive controls. Known local remedy is therefore present for the legitimate folded defect. Qualification of the original SQL fixture and retained stale-bool pins is still pending; this is not a blanket test-suite pass or invalid closure.
- Review corrections: Changed uncertain/unknown/unknown/keep_open to valid/known/no/fixed_pending_verification for the mixed record after identifying the exact bare-nil repair and regression source. Strict-bool premise is separately stale; repaired real defects stay valid.

## phase_profile_flag_unusable_seed_missing_rt_heap_registry_count_2026-07-20 — Phase-profile tracing breaks every rv32 firmware build: `rt_heap_registry_count` missing from the seed

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/phase_profile_flag_unusable_seed_missing_rt_heap_registry_count_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_log_helpers.spl:28; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_log_helpers.spl:67
```
- Review rationale: Full report retracts unconditional failure: firmware wrapper sets SIMPLE_COMPILER_PHASE_PROFILE. Current driver_phase_trace_enabled retains both flags; log_phase (127-140) emits timing and _append_phase_profile (67-79), with no heap-registry count. This removes the reported direct call but introduces a separate sink contract. History -S identifies 93e36952728; removal diff/provider qualification not inspected, so no known root remedy or full firmware completion admitted. Remaining gap: Inspect 93e36952728 removal diff and qualify profiling-enabled firmware path with the admitted artifact.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. Research proposed known/no/fixed_pending_verification; retained unknown/unknown/keep_open because removal history and profiling provider were not fully qualified.

## pid1_target_service_manager_missing_2026-08-11 — Missing target-native PID1 service manager

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pid1_target_service_manager_missing_2026-08-11.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/init/service_manager_main.spl:75; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/services/init/service_manager_main.spl:139; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/boot/pid1_launch.spl:73
```
- Review rationale: Full report distinguishes preparatory PID1 authority from lifecycle acceptance. Current service_manager_main bootstraps VFS/net/HTTP in order, waits for named endpoints, unwinds failed starts and has bounded backoff/dependent quarantine. Target-bound search across src and scripts found pid1_prepare_into_scheduler only in its owner/wrapper and no SIMPLEOS_PID1_BINARY/REQUIRE_PID1 path; report image-bake claims therefore are not demonstrated at this target. Missing boot integration remains a real requirement, not grounds for invalidity. Remaining gap: Locate successor architecture boot/image producer and obtain provenance-valid QEMU launch/reap/restart receipt; absent caller is not proof every boot path is absent.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## placeholder_lambda_as_fn_param_callback_unevaluated_2026-07-20 — Placeholder lambda (_1 + 1) passed to a user free-function param is never invoked

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/placeholder_lambda_as_fn_param_callback_unevaluated_2026-07-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_expr.spl:683; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/placeholder_lambda.spl:142; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/frontend/fixtures/placeholder_lambda_callback_value_probe.spl:18
```
- Review rationale: Read full report including September correction: outer consumer triggers historical lambda leakage; standalone value-bound callbacks passed, contradicting never-invoked title. Current parse_call_arg enters/restores higher-order depth and transforms each argument; placeholder owner increments only for recognized higher-order callees. Fixture contains real nested expect(pmap(...,_1+1)) equality with named and explicit controls. AST shape and source ownership do not establish callable runtime execution; keep historical validity with unknown remedy. Remaining gap: Admitted interpreter/native callback-value result and eval_call binding trace remain absent.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## placeholder_lambda_scoping_nested_ordinary_call_2026-08-31 — Placeholder-lambda (`_1`) scoping breaks for an ordinary call nested inside another call's argument

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/placeholder_lambda_scoping_nested_ordinary_call_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/expressions/postfix.rs:43; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/expressions/helpers.rs:621; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/placeholder_lambda.spl:142
```
- Review rationale: Full report identifies Rust ordinary nesting counter swallowing index_of_func placeholder. At target postfix.rs 43-57 still defers ordinary callees whenever call_arg_depth>0; recognized list 71-94 excludes index_of_func and helpers.rs increments for arguments. Pure-Simple differs materially: _ph_ho_arg_depth increments only inside a recognized higher-order argument, and parser caller restores depth before transformation. Thus seed diagnosis remains source-supported while same defect cannot be imputed to current pure-Simple semantics; explicit lambda remains a workaround. Remaining gap: Qualify original nested ordinary-call form and higher-order nesting controls on an admitted pure-Simple artifact; generic suffix addition is not an established root remedy.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. Rejected low known/no/fix_candidate based on adding callback names: that does not establish general scope ownership, and pure-Simple depth semantics differ from Rust.

## platform_module_shadowing_and_unknown_import_segv_2026-09-01 — `platform.spl` shadowed by `platform/__init__.spl`; an unknown import SEGVs mute

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/platform_module_shadowing_and_unknown_import_segv_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/platform.spl:3; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/platform/__init__.spl:13; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/path_pure.spl:55; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_entry_closure_core.spl:998; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_source_pipeline_loading.spl:1154
```
- Review rationale: Full report separates Windows seed import crashes, duplicate platform modules, and basename separator policy. Current std.platform still wildcard-exports nogc_sync_mut.platform and both file/directory definitions exist; the directory delegates detection through an alias to avoid a separate self-recursion issue. path_pure.last_component 55-70 still scans slash only, matching the documented Windows differential mismatch. This establishes a real historical multi-cause defect but not a unified source remedy or universal POSIX failure. Independently checked new frozen low lead: driver entry resolver returns base.spl before package __init__; source-loading reports/logs missing dotted modules. These differ from seed report, and module-file errors do not demonstrate missing-export diagnostics. Remaining gap: Loader successor search at historical 05.loader path was empty; trace actual module precedence and unresolved-import diagnostic owner before assigning root fix. Preserve POSIX backslash-as-data.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## plugin_bare_unit_or_owner_workaround_2026_10_10 — Plugin bare unit OR alternatives lose enum owner

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/plugin_bare_unit_or_owner_workaround_2026_10_10.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_types.spl:33; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_vhdl/_VhdlProcess/process_codegen.spl:62; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/plugins/backend_cuda/cuda_backend.spl:329
```
- Review rationale: Full report explicitly labels workaround/follow-up unexecuted. Actual LocalKind declares Var/Temp/Return units; VHDL emit_process_dest_assign now qualifies Var|Temp and preserves distinct Arg rejection and assignment bodies. CUDA comparison arms qualify MirBinOp and PrimitiveType while retaining Bool-destination and same-operand-type checks. These are active semantic workarounds, not restored contextual bare-unit owner propagation. No root remedy asserted. Remaining gap: Complete remaining plugin declaration/caller map and contextual binder/owner first-loss trace; qualify original bare alternatives and Opaque payload mismatch negative control.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## poll_unwrap_second_bind_site_lower_and_check_impl_2026-08-25 — `Poll.unwrap` steals `.unwrap()` in `lower_and_check_impl` — a SECOND, independent bind site

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/poll_unwrap_second_bind_site_lower_and_check_impl_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:1086; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:1164; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs:932; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1729
```
- Review rationale: Read both initial disassembly and August 31 correction: a small imported-decoy reproducer supersedes the no-fixture claim. Current mangle.resolve_method_call_static still performs successful resolve_name_variants rebind before enum-helper guard in else, whereas bare text methods are protected first. Comment explicitly records hoisting enum guards broke valid text-option helpers. Source supports the indicated second site, but does not observe the actual lower_and_check_impl binding or prove a safe narrow predicate. New low evidence independently checked: a separate call-target resolver has early bare-enum protection at 932, while inspected method resolver retains post-success hazard; driver retained surfaces now uses direct streaming owner instead of unwrap. Do not conflate these two mangle routes or workaround with general repair. Remaining gap: Instrument success binding in admitted reproduction with Poll/FailSafe decoys and valid Option helper controls; root remedy remains unknown.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## posix_gated_runtime_symbols_invisible_on_windows_2026-08-31 — POSIX-gated runtime symbols "invisible on Windows" — the 90 is REFUTED; the real gap is file selection, not `#if`

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/posix_gated_runtime_symbols_invisible_on_windows_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:571; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/build.rs:444
```
- Review rationale: Full report retracts the 90-symbol population while retaining actual target file-selection and guard defect. Target tools.rs still adds hosted_win32.c only in Linux branch; runtime/build.rs 444-445 excludes it on Windows in this source list. Thus corrected issue remains meaningful despite false initial count. Full preprocessor census and Windows artifact equivalence were not rerun; no invalid closure and no assertion of current exact 11/42 populations. Remaining gap: Reconcile all provider source lists and per-target artifact-backed guard contract, then obtain Windows link evidence; inspected branch alone does not prove total link availability.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## pr255_host_path_native_corrupts_posix_paths_and_costs_unix_2026-09-02 — PR #255 `host_path_native` corrupts POSIX filenames and taxes every Unix file op

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pr255_host_path_native_corrupts_posix_paths_and_costs_unix_2026-09-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/fs/host_path.spl:93; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/fs/host_path.spl:97; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/fs/host_path.spl:142; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/file_ops.spl:97; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/nogc_sync_mut/fs/host_path_spec.spl:85
```
- Review rationale: Read report through resolution and foreign-commit warning. Target host_path_native_for returns POSIX input before replacement; host_path_native tests cached host flag before conversion; MinGW recognition requires leading / and lowercases only that drive. file_ops still calls this boundary for exists/read/size/write. Target ancestry includes source in 88aac2ffe28 and subsequent absolute-path additions. Historical defect is valid and concrete bounded identity-first correction is present, but no current POSIX byte/performance or Windows long-path qualification is claimed. Independently read exact-content relative-drive, native idempotence and host-boundary/long-path regression assertions; no test executed. Remaining gap: Run retained byte-content/relative-drive controls and cached-guard measurements with admitted runtime; report eight-commit cherry-pick recipe is obsolete for this present owner.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. Queue unknown/unknown/keep_open becomes known/no/fixed_pending_verification for demonstrated bounded path-identity correction, not runtime PASS.

## preexisting_main_gate_debt_blocking_all_prs_2026-08-31 — Pre-existing main gate debt blocking every PR (recorded offender list)

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/preexisting_main_gate_debt_blocking_all_prs_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:.github/workflows/aot-lane-fences.yml:159
```
- Review rationale: Read complete ledger including later stale push-must-check entry and prohibition on general waiver. One recorded offender has current wiring: aot-lane-fences invokes check-context-pack-reduces at 159. That narrows historical unwired debt, but neither establishes current hygiene census nor source-fingerprint manifest regeneration. Historical baseline blockage remains valid; no current all-PR failing claim and no bypass endorsed. Remaining gap: Reconcile exact historical hygiene offenders and current must-check fingerprint ownership in isolated source; current green checks/manifest receipt absent.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## prelude_builtins_rebindable_by_transitive_import_2026-08-10 — 50 prelude builtins beyond `exit` remain silently shadowable by a transitive top-level fn

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/prelude_builtins_rebindable_by_transitive_import_2026-08-10.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/mod.rs:670; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_eval.rs:403; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl:57
```
- Review rationale: Report corrections reject existence-only shadowability counts and distinguish native HIR fallback from actual fence. Current Rust evaluate_call 670-690 forces PRELUDE_UNSHADOWABLE exit through extern builtin, warns for other prelude names, and subsequent builtin_wins gate respects user definitions. Current constant contains only exit. Pure-Simple is_interp_builtin_fn moved to _Expressions/expression_support; merely adding names to fallback is not proved a dispatch fence. Historical issue remains real; late Rust warning policy cannot close native scope. Remaining gap: Trace current pure-Simple symbol lookup and target signal before a target-conditional exit fence; qualify value-discriminating transitive imports per lane, preserving baremetal owners.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## prepush_hook_unpassable_native_build_oom_2026-08-17 — Pre-push hook is unpassable: check-native-extern-fabrication depends on native-build which is SIGKILLed at >24

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/prepush_hook_unpassable_native_build_oom_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-native-extern-fabrication.shs:418; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-native-extern-fabrication.shs:457
```
- Review rationale: Full report separates measured env-width retention from one absurd 16-GiB allocation; source discovery, duplicate loading, and JIT switch are expressly ruled out. Current extern gate still requires control output ctrl-ok/exit7 and checks absent-symbol name before accepting nonzero compile as refusal. Control build failure and unrelated absent-case failure are printed FAIL, not proof fabrication was fixed. No current resource receipt or allocation-stack capture establishes root solution. Remaining gap: Qualify small fixture resource use and capture large-allocation owner on admitted runtime. Keep worker failure distinct from the guarded extern property; bypassing guard is not remedy.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## prepush_ratchet_guards_preexisting_red_blocks_unrelated_lanes_2026-08-16 — Pre-push ratchet guards fail full-scan, blocking lanes that introduce nothing

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/prepush_ratchet_guards_preexisting_red_blocks_unrelated_lanes_2026-08-16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-engine-claiming-specs-use-probe.shs:142; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-engine-differential.shs:87; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-native-trailing-default-param.shs:246
```
- Review rationale: Complete report records identical historical offenders at base/tip, not a waiver for arbitrary PRs. Current engine-claiming guard supports --ref and baseline modes with explicit empty-tree ERROR; differential guard distinguishes harness ERROR/no count from FAIL; trailing-default guard treats signal build as ERROR. This is stronger outcome discipline but does not itself establish safe range-based policy for runtime gates. Generic delta conversion cannot be called a known repair without preserving actual semantic checks. Remaining gap: Trace current hook invocations and accepted per-gate scope contract; reconcile historical four offenders and present baseline without weakening protection.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## prevention_mock_deferred_arming_impossible_2026-08-07 — std.spec prevent/prevent_at_most cannot defer arming; no module state across it examples

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/prevention_mock_deferred_arming_impossible_2026-08-07.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:373; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:1159
```
- Review rationale: Full report records three independent constraints: stored mock identity, cross-example globals, wildcard facade. Current prevent/prevent_at_most immediately construct/check ForbiddenCallGuard; prevent_file documents immediate alias, not deferred arming. _execute_it invokes hooks/body and clears shared error array; no deferred prevention queue appears in inspected lifecycle. Thus shipped API remains workaround and historical requirement is real, but source does not diagnose current interpreter identity or prove architectural change necessary. Remaining gap: Inspect interpreter capture/global ownership and current facade export enumeration with stored-identity and cross-example controls before choosing semantic change.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## primitive_receiver_trait_impl_dispatch_2026-08-07 — Trait impl on primitive Self honoured only by interpreter; JIT fails open, native SIGSEGVs

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/primitive_receiver_trait_impl_dispatch_2026-08-07.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve.spl:103; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve.spl:326; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve_strategies.spl:176
```
- Review rationale: Read original defect split and substantive late execution/correction sections (not every historical iteration). Target resolver now keys primitive receivers by signedness/width, registers primitive trait owners, and falls through to structural solver instead of returning nil. This independently supports the report partial pure-Simple repair. Later seed i32/i64 collapse, unsigned missing impl and builtin-name JIT bypass are distinct; source repair does not validate them or the default-method residual. No blanket known solution. Remaining gap: Inspect default-method owner registration and seed receiver-gated dispatch separately, then obtain true pure-Simple primitive width/unsigned/default-method execution; historic seed probes do not run edited compiler.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## print_raw_builtin_unknown_to_selfhosted_hir_2026-09-03 — `print_raw` is a Rust-seed builtin the self-hosted HIR does not know

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/print_raw_builtin_unknown_to_selfhosted_hir_2026-09-03.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/tui/terminal.spl:37; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:3787; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/simple_core/core_string.spl:1983
```
- Review rationale: Full report identifies unresolved bare print_raw, not proven independent len/substring faults. Target terminal now declares extern print_raw(data:text)->i64 and uses it for write/flush. Native C print_raw and pure core_string providers exist and take tagged i64, writing then returning zero (C also flushes). Declaration changes resolution but provider presence does not establish text ABI conversion/closure selection. Remaining gap: Inspect emitted text-extern ABI mapping and selected runtime provider on devhub closure, then qualify terminal writes.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## private_symbol_collision_sshd_four_names_2026-07-28 — Private cross-module symbol collision mis-dispatches silently under JIT; C1/C2 not landed

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/private_symbol_collision_sshd_four_names_2026-07-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1917; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:848
```
- Review rationale: Full report says four original sshd warnings benign in-range, while same-parameter/different-return synthetic wildcard collision misdispatches. Target lowerer collects only parameter TypeIds and leaves identical signatures last-write-wins; direct calls fall from exact match to unique arity then candidates.last absent extern. This supports general defect independently of source renames. Return type in key alone does not prove module-correct call selection. Remaining gap: Trace module-qualified caller ownership and same-argument/different-return discriminator; do not attribute f-to-e parser symptom to equivalent nibble bodies.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## process_transfer_session_replay_identity_2026-08-12 — Transfer session identity uses FNV-1a over 31 PID bits, which is not authentication

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/process_transfer_session_replay_identity_2026-08-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/structural/transfer/process_frame_auth.spl:26; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/parent_commit_piped_process.spl:186; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/parent_commit_piped_process.spl:302
```
- Review rationale: Read all amendments including contradictory FNV-only/source-complete claims. Target HMAC covers wire/session/generation, compares full 64-char tag, and reader gates inbox offer on decoded/authenticated success. spawn_authenticated creates authenticated reader; legacy create sets auth_required false. FNV presence does not refute V2 but compatibility selection matters. One HMAC boundary PASS does not qualify all process transport. Remaining gap: Audit legacy constructor callers and supplied child_identity versus spawned pid, authority freshness, PID reuse/namespace/exec/revocation qualification.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## production_gui_font_offload_runtime_readback_2026-06-23 — Bug: Production GUI font offload lacks runtime glyph readback

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/production_gui_font_offload_runtime_readback_2026-06-23.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-production-gui-font-offload-evidence.shs:117; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-production-gui-font-runtime-evidence.shs:265
```
- Review rationale: Full report requires real accelerator submission and returned vector/bitmap evidence. Outer evidence wrapper invokes runtime script and consumes fields; runtime owner runs vector and Metal/CUDA/OpenCL children, requiring pass/ready, positive accelerator attempts and returned glyph/pixel counts plus backend readback PASS. This is an active gate with missing execution evidence; no invalidity or lowered requirements inferred. Remaining gap: Inspect selected native font/readback producer checksum provenance and obtain actual accelerator receipt; wrapper conditions do not establish glyph submission.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## project_statistics_selfhosted_generation_blocked_2026-08-13 — bin/simple stats --quality=summary refuses to run because the binary is the Rust seed

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/project_statistics_selfhosted_generation_blocked_2026-08-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/stats/inventory_scan_v2.spl:55; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/stats/inventory_scan_v2.spl:82
```
- Review rationale: Complete report scopes resolution to generated report/PPTX package, while stats CLI still rejected seed and native Office conversion remained blocked. Current stats_scan_tree rejects file_is_symlink before is_dir recursion; collect_stats_inventory_v2 traverses six intended roots and aggregates facts. That concretely addresses double-count/loop risk, not current CLI provenance or independent generated-package validation. Closed bookkeeping is not invalidity. Remaining gap: Locate retained nine-slide PPTX validation receipt and qualify current self-hosted stats route separately; no global root remedy assigned from symlink guard.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## promise_new_push_reassign_same_scope_as_nested_closure_2026-07-29 — Module-array push+reassign reads stale when the same fn also defines a nested closure

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/promise_new_push_reassign_same_scope_as_nested_closure_2026-07-29.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/nogc_async_mut/promise_spec.spl:84; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/nogc_async_mut/promise_spec.spl:103
```
- Review rationale: Full report identifies local spec Promise, explicitly different from production API. Historical path moved: target test/01_unit/lib/nogc_async_mut/promise_spec.spl contains _promise_new_push_pending hoist and new(executor) invokes nested resolve/reject then reads shared state. This preserves the exact workaround/control shape and establishes original stale-read context; helper hoist is not interpreter environment repair. Remaining gap: Trace nested capture/module rebinding owner with original inline versus helper control. Current runtime environment storage semantics were not established.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## provider_query_result_v2_wire_codec_missing_2026-09-13 — `SimpleProviderQueryResultV2` wire codec is missing; `os/smf/provider_query_wire.spl` imports nonexistent digest symbols

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/provider_query_result_v2_wire_codec_missing_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/composition/provider_contract.spl:23; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/smf/provider_query_wire.spl:30; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl:98
```
- Review rationale: Full report missing V2 and stale digest imports predates target contract. Target V1 explicitly uses eight u32 digest words, 84-byte size and digest at 48/reserved80; wire imports correspond to that rich contract. Target spec still imports V2 and calls encode/decode V2, while named owners have no such symbols. Test text still says 60-byte V1, so applying report scalar-V1 recipe would contradict present ABI. Historical defect valid, migration remedy unknown. Remaining gap: Resolve admitted ABI/version compatibility and spec migration before adding V2; inspect provider_loader/native_provider callers and exact fix history. No 60-byte rollback justified.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.

## pure_backend_naked_fn_gaps_2026-08-28 — Pure backend @naked gaps: alloca suppression + E-NAKED validation seed-only; ~{memory} default delta

- Source receipt: `adjudication_v2_16`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pure_backend_naked_fn_gaps_2026-08-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:301; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:907
```
- Review rationale: Full report distinguishes naked alloca/validation, memory-clobber defaults, and align bytes versus RISC-V power. Current core_codegen stamps naked noinline, suppresses readonly/alwaysinline for naked and emits align value directly; it then translates every block. Its separate SSA alloca transform remains present. No E-NAKED diagnostic was found in searched pure MIR/backend scope, but that bounded search does not prove absence in all validation owners. Present attributes alone do not prove safe naked body. Remaining gap: Trace entry validation/alloca emission and raw-asm clobber defaults with nonempty naked body; decide documented alignment semantics before asserting one remedy.
- Review corrections: Independent target-bound adjudication; historical execution remains untested. No invalid closure or unverified whole-report fix inferred.
