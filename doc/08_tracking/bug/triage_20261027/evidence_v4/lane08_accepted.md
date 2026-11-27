# V4 lane 08 accepted evidence

Accepted classifications in V4: 157. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

- 43 accepted records are inherited field-for-field from V3; their detailed evidence is preserved in [V3 lane 08 evidence](../evidence_v3/lane08_accepted.md).

- 114 additional accepted records are detailed below.

## stage2_exit127_llvm_mingw_path_dll_clash_2026_10_26 — stage2.exe exits 127 silently (0xC0000139 libLLVM-23.dll clash) with llvm-mingw first on PATH or SIMPLE_PROJECT_ROOT set

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_exit127_llvm_mingw_path_dll_clash_2026-10-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/bootstrap_main.spl:1; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-phase-verification.shs:583
```
- Review rationale: Full report targets silent loader failure with libLLVM-23.dll/0xC0000139, not ordinary CLI error handling. Current verification helper prepends a located LLVM-C.dll directory for delegated seed probes, a distinct DLL/missing-DLL scenario; bootstrap_main can only run after loading. Scoped bootstrap/launcher search found no libLLVM-23.dll handling. Exact direct stage2.exe launch/import identities and project-root trigger remain unresolved; PATH order is only the reported workaround.
- Review corrections: LLVM-C.dll seed delegation is distinct from the reported libLLVM-23.dll entry-point clash; no launcher/root repair inferred.

## stage2_link_undefined_cpu_probe_and_surface_symbols_2026-09-13 — Site 17: Stage 2 fails to LINK — 6 undefined symbols on aarch64-apple-darwin

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_link_undefined_cpu_probe_and_surface_symbols_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/module_surface_registry.spl:608; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:662; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/runtime_compiler.spl:624; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/runtime_compiler.spl:725; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:19417; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/value/sffi/env_process.rs:1931
```
- Review rationale: Checked all three symbol classes. module_surfaces_promote_reason is defined and the bool wrapper calls it; mir_type_is_scalar_numeric now calls its own _sffi_method_hir_type_discriminant. Current runtime_core_c_sources_v1 includes runtime_native, selected for core-c-bootstrap; that C owner defines arch probes and CPUID-related entrypoints, while Rust also has unmangled arch gates. This resolves a current source-list question left by research, but historical emitted archive composition and current macOS link success remain unqualified. No single root remedy for the aggregate is certified.
- Review corrections: Added actual core-c-bootstrap source selection and C/Rust CPU providers. Research runtime build.rs line reference was unrelated audio commentary; do not infer active provider absence from it.

## stage2_matrix_full_cli_build_exceeds_40g_2026_10_19 — Stage 2 matrix full-CLI build peaks above 40 GiB in MIR lowering (41.8 GiB, OOM-killed under a 40G scope)

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_matrix_full_cli_build_exceeds_40g_2026_10_19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:3432
```
- Review rationale: The full report preserves both 2702-module MIR OOM and later HIR growth after ABI-trace opt-in, with separate concurrent process pressure. Current lower_module_emit_all stores module.functions.values in an owner field replaced per module and feeds each bound function to emission. That establishes a real retention boundary but no attribution of the tens of GiB growth to it. Historical measurements are credible; current fixed-graph phase allocation/retention profile and aggregate process accounting remain missing.

## stage2_mir_shard_flat_pool_text_len_minus1_2026_10_22 — stage2 mir shard flat pool text len minus1 (workaround registered)

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_mir_shard_flat_pool_text_len_minus1_2026-10-22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1526; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:1778; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/flat_pool_codec.spl:605
```
- Review rationale: Research stopped at early Update 7. The full 1276-line report later retracts wrong-pool probes, promotion/reclaim-only cures and split-specific codegen inference. Lane61 reports clean frontend measured boundaries in its instrumented configuration, a deterministic post-seal HIR-worker null lookup dereference, and allocation-order perturbation across candidates; it explicitly says the corruptor was not observed. Current bridge supports both legacy blob and packed restore, promotes module/blob/pool owners, then ends scope before resets; codec has graceful poisoned-capture refusal. These protections do not establish cause or cure. Keep valid historical failure with unknown solution/structure, without another execution cycle.
- Review corrections: Reject Update-7 lifetime mechanism as established current diagnosis: subsequent report corrections refute or narrow it. Full latest history identifies allocation-order-sensitive manifestations and an observed HIR null lookup, not a proven pool-reclaim cause. No new verify/fix cycle allowed or performed.

## stage2_multiline_if_continuation_2026-08-14 — Stage 2 multiline `if` continuation divergence

- Source receipt: `adjudication_v2_24`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_multiline_if_continuation_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer_struct.spl:290; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer_struct.spl:333; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer_struct.spl:1362; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer_struct.spl:1479; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl:84; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/frontend/lexer_if_condition_leading_and_continuation_spec.spl:139
```
- Review rationale: Current line_starts_binary_op recognizes word and only at a boundary; leading_op_continues requires expression-ending prior token and deeper indent. Both newline scan and indentation handling call it and suppress their token on success. The dedicated spec directly invokes lex_init/lex_next, checks no newline before and, retains block/same-indent negative controls, and requires EOF under a cap. This supports a narrow source remedy while historical seed-driven lexer PASS is not an admitted current Stage2 qualification.

## stage2_native_build_timeout_zero_immediate_2026-08-24 — Stage-2 native-build treats `--timeout 0` as immediate timeout

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_native_build_timeout_zero_immediate_2026-08-24.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/native_build_main.spl:306; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/process_ops.spl:14; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/process_ops.spl:1796; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/parallel.spl:924; ancestor repair 73d8e2c53d851a29dcb8a829d3d520d6f41345c9 (diff inspected)
```
- Review rationale: Report records 709 immediate zero-budget timeouts. Independently traced native_build_timeout_ms (explicit zero survives parsing), the app.io facade to the library live-process owner, and the elapsed loop's effective_timeout == 0 branch. Ancestor 73d8e2c53d8 changes both parser acceptance and deadline handling; this is a concrete local zero-unlimited correction. It does not qualify a current Stage2/3 artifact.
- Review corrections: frozen queue solution: unknown -> known; frozen queue structural_change: unknown -> no; frozen queue recommended_action: keep_open -> fixed_pending_verification

## stage2_native_class_field_text_dict_owner_lost_2026-09-14 — Stage-2 native codegen: `imported enum has no declaration owner` on a plain single-hop import

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_native_class_field_text_dict_owner_lost_2026-09-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_build.spl:167; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:778
```
- Review rationale: The minimal Holder probe reports text-valued class-field Dict reads returning a raw word. Current imported_enum_owner_module reads a row mirror then symbol metadata; registration pushes the mirror. Both the full report and source explicitly call this a workaround. Later addenda retain a full-closure HIR wedge after five mitigations. Bypassing this consumer does not repair native Dict storage/read codegen, so a root solution and required structural scope remain unknown.
- Review corrections: V2 research solution: known -> unknown; V2 research structural_change: no -> unknown; V2 research recommended_action: fixed_pending_verification -> keep_open; Reject research known/no/fixed_pending_verification: enum owner mirror and symbol-table read are consumer mitigations, not a repair of the tracked native Dict defect.

## stage2_native_codegen_silent_wrong_values_aarch64_2026-09-05 — Stage-2 native codegen produces silently wrong values on aarch64

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_native_codegen_silent_wrong_values_aarch64_2026-09-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:834; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/simple_core/core_array.spl:764
```
- Review rationale: Five historical AArch64 wrong-value/crash probes remain distinct: function values, map, closure invocation, Dict.len, and missing Dict.size. Current Cranelift CallIndirect translates operands and invokes a typed signature; pure-core rt_dict_len returns the length field after pointer validation. Those concrete owners do not diagnose the old binary's ABI or missing-method behavior. Preserve valid historical report, unknown remedy and untested current behavior.

## stage2_native_compile_segv_after_unwrap_fix_2026-08-25 — Stage-2 hello world SEGVs in `native_compile` (step 5/6) — newly exposed by the unwrap-theft fix

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_native_compile_segv_after_unwrap_fix_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:2547; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:2731
```
- Review rationale: The full report reaches native_compile after successful MIR/cache phases and explicitly distinguishes earlier unwrap theft. Current phase owner logs entry then builds frozen capsules via ParallelBuilder. No stack in the report identifies which operation crashed; matching rc139 is insufficient attribution. Keep the historical defect open with unknown remedy.

## stage2_native_f64_arithmetic_lowered_as_integer_ops_aarch64_2026-09-05 — Stage-2 native codegen lowers f64 `+ - * /` as integer ops on the raw bit patterns (aarch64)

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_native_f64_arithmetic_lowered_as_integer_ops_aarch64_2026-09-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_lowering_stmts.spl:542; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:5123; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_data.spl:510
```
- Review rationale: The report's finite bit-pattern predictions establish historical integer arithmetic on f64 bits; its comparison discussion is not a reliable general ordering proof. Current binop lowering selects F64 when local_is_float observes F32/F64 from MirBuilder.local_type. I checked that consumer and lookup; the flat-path metadata producer that failed historically remains unlocalized. Do not infer a current fix or patch arithmetic based solely on this guard.

## stage2_native_method_scoped_dict_field_write_segfaults_2026-09-14 — Stage-2 native codegen: SEGVs compiling a method that writes a `self.<dict>[k] = v` inside a guarded `if`

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_native_method_scoped_dict_field_write_segfaults_2026-09-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:794; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_symbol_table_methods.spl:258; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/mir/external_layout_reference_nil_info_guard_source_spec.spl:27
```
- Review rationale: Later report corrections decisively replace the Dict-write hypothesis: record_external_layout_reference called stolen Poll.unwrap and dereferenced raw zero, which a nil-sentinel guard missed. Current scalar symbol readers and source-shape spec remove that call site; the report records a historical successful rebuilt probe. This is a proven consumer mitigation while the producer unwrap misbinding remains explicitly open, not a root repair established by this review.
- Review corrections: V2 research solution: known -> unknown; V2 research structural_change: no -> unknown; V2 research recommended_action: fixed_pending_verification -> keep_open; Downgrade research known/no/fixed_pending_verification to unknown/unknown/keep_open: source and report explicitly retain the open unwrap producer defect; source-shape pins and historical bypass success do not fix it.

## stage2_positional_entry_segv_module_surfaces_null_2026-08-31 — Stage-2 self-hosted compiler SEGVs on a positional entry — `module_surfaces` reads as NULL

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_positional_entry_segv_module_surfaces_null_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1719
```
- Review rationale: The report's disassembly and A/B establish Option.unwrap rebound to another provider before module-surfaces construction, not an uninitialized registry. Current lower_and_check path avoids unwrap and uses the retained direct owner with formation checking. The report explicitly says this original HIR crash disappeared after rebuilding; later CompileContext.has_errors failure is separate. Retain fixed-pending verification for this narrow symptom, but the seed method-resolution root repair is not established.
- Review corrections: V2 research solution: known -> unknown; V2 research structural_change: no -> unknown; frozen queue recommended_action: keep_open -> fixed_pending_verification; Retain narrow fixed_pending_verification from historical post-change trace, but downgrade known/no root solution to unknown/unknown: the present direct-owner/?? route avoids the producer defect rather than repairing dispatch.

## stage2_positional_native_build_fails_in_capsule_collection_2026-09-06 — Stage-2 positional native-build fails in the capsule-collection checkpoint, silently

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_positional_native_build_fails_in_capsule_collection_2026-09-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:1234; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/incremental.spl:863
```
- Review rationale: Historical LLVM candidate emits an object and receipt but leaves cache empty. Current collector separately checks result identity, frozen/disk source identity, receipt, durability and source fingerprint before cache publication. FileFingerprint now uses byte SHA-256, but that does not identify the original failed sub-check, especially since recorded size came from a separate call. No fix attribution or cross-backend substitution is supported.

## stage2_pure_simple_compile_paths_crash_2026-08-28 — Stage2 pure-Simple compiler: `compile` and single-file `native-build` crash or fail on ordinary modules

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_pure_simple_compile_paths_crash_2026-08-28.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/bootstrap_main.spl:455; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_lowering_stmts.spl:2088
```
- Review rationale: Report separates parse/struct/use crashes from module-global assignment failures and distinguishes an explicit-entry backfill route. Current bootstrap dispatch has distinct positional and explicit-entry routes; MIR assignment now emits StoreGlobal for recognized globals before rejecting missing locals. This source support does not establish which reported crashes or old flat-path binding errors survive on the frozen candidate. Unknown remedy remains appropriate.

## stage2_receiver_bootstrap_fn_registry_promotion_failed_2026-09-13 — Stage-2 receiver probe: `bootstrap fn registry promotion failed` on the site-13 gate fixture

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_receiver_bootstrap_fn_registry_promotion_failed_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2490; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_data.spl:2935
```
- Review rationale: The report's failure is fn-registry promotion, not the earlier missing-link symbol. Current caller still returns one aggregate promotion-failed message; owner performs wholesale registry promotion on adoption and journal/delta promotion thereafter. Its conjunction loses the individual failed registry identity. Neither the wrapper refactor nor module naming can be selected as cause without that identity.

## stage2_sanity_diagnostic_staging_unavailable_2026-09-12 — Stage 2 sanity fails: secure_temp_dir returns "" during AOT diagnostic staging

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_sanity_diagnostic_staging_unavailable_2026-09-12.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/file_ops.spl:196
```
- Review rationale: Full Windows report rules out the obvious parent-path/SystemRoot explanations through direct probes, yet those probes omitted the failing entry-closure harness route. Current secure_temp_dir_raw admits heap-built parent and prefix through separate setters and zero-argument make, returning empty on refusal. This different ABI shape is not proof of a repair for the historical harness-only staging failure. Keep unknown remedy and current untested status.

## stage2_sanity_module_path_naming_probe_segv_2026_10_22 — stage2 sanity module path naming probe segv (workaround registered)

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_sanity_module_path_naming_probe_segv_2026_10_22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/generated/hir_visitor.spl:202; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/native_build_cache.spl:17; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/native_build_output_mode.spl:17
```
- Review rationale: Read the full multi-update report: earlier flatten/metadata hypotheses failed or only moved the frontier; final October24 update reports Stage2 admission after a chain of fixes. Independently checked ArrayLit fold visitor explicitly unwraps Some before walk_hir_type and both env-restore owners unwrap text? before sosix_env_set. These directly address two diagnosed faults; a current artifact and the complete promotion/codec chain are not qualified here. Retain historical fixed-pending status without claiming every aggregate producer has a known root repair.
- Review corrections: V2 research solution: known -> unknown; frozen queue recommended_action: keep_open -> fixed_pending_verification; Downgrade research solution known to unknown for the whole multi-site record; confirmed fold/env repairs are narrower than complete class/codec/promotion root repair. Preserve the report's final admission evidence as historical, not current execution.

## stage2_sanity_passes_share_one_object_store_2026-09-13 — Stage-2 sanity's two frontend passes share one object store despite separate `--cache-dir`s

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_sanity_passes_share_one_object_store_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs:734; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/bootstrap_main.spl:590; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/io/native_build_cache.spl:10; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl:884
```
- Review rationale: The report's order-inversion probe traced both sanity passes to one native object store despite distinct CLI cache directories. Current positional bootstrap route snapshots, parses, binds and restores the requested cache around driver compilation; native_build_cache_bind sets the very environment variable consumed by driver_native_build_cache_dir. The gate still supplies per-probe paths. This is a concrete local forwarding repair, awaiting current two-pass qualification.
- Review corrections: frozen queue solution: unknown -> known; frozen queue structural_change: unknown -> no; frozen queue recommended_action: keep_open -> fixed_pending_verification

## stage2_sanity_reverse_reference_publish_refused_2026_10_22 — Stage 2 sanity: transient HIR scope end failed on p2_add -- reverse-reference publish chain refuses in the self-hosted candidate

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_sanity_reverse_reference_publish_refused_2026_10_22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/00.common/cache/reverse_reference_facts.spl:172; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/00.common/cache/reverse_reference_facts.spl:277; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:3250
```
- Review rationale: Full report distinguishes transient publish refusal from cache-store noise, records corrupted promoted-batch scalars, then labels scalar mirrors a workaround. Current seal explicitly promotes array limbs/elements and publish checks module-global scalar mirrors. The runtime promotion entry classifies ownership and permits already-immortal roots; none of this proves a root class-layout/copy repair. Keep the defect open, with exact current promotion/runtime attribution unresolved.

## stage2_split_impl_modules_missing_from_entry_closure_2026-08-22 — Stage 2 omits split impl providers from the native entry closure

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_split_impl_modules_missing_from_entry_closure_2026-08-22.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl:23; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/match_desugaring.spl:986; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/35.semantics/resolve.spl:26
```
- Review rationale: The report names six unresolved methods whose two split-impl providers had no import edges, and reports Phase2 linkage recovery only. Current match_desugaring imports union_narrow_arms and invokes it; resolve imports resolve_lookup_helpers. These explicit owner-to-provider edges are a bounded source remedy, while focused specs and Stage3 linkage remain unqualified.
- Review corrections: frozen queue solution: unknown -> known; frozen queue structural_change: unknown -> no; frozen queue recommended_action: keep_open -> fixed_pending_verification

## stage2_stage3_route_native_compile_timeout_2026-09-13 — Site 9: Stage 2's Stage-3 route allocates without bound in `native_compile` (killed at 124)

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_stage3_route_native_compile_timeout_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/parallel.spl:274; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/function_lowering.spl:186; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_lowering_types.spl:855
```
- Review rationale: Full report supersedes both graph-size and nonshrinking-pop theories: the original DFS exit used presence on an empty array; later pop.unwrap and full local-symbol-index loops were distinct failures. Current DFS uses length/index slicing, function reset clears local_symbol_index_slots, and insertion probing is capacity-bounded with rebuild. Those concrete mitigations/repairs do not establish complete route recovery or a fix for the underlying collection optional ABI; duplicate LLVM definitions are another separately reported frontier.

## stage2_test_runner_imported_enum_owner_text_corrupt_2026_10_19 — Stage 2 test-runner build reads overwritten imported-enum owner text (schema=...) and fails MIR enum lowering

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_test_runner_imported_enum_owner_text_corrupt_2026_10_19.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl:778; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_types.spl:109; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_symbol_table_methods.spl:316; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:275
```
- Review rationale: The report records owner strings overwritten by build-progress schema bytes. Current import registration stores Some(imported_mod.module_name) in HirSymbol; enum_qualified_key reads that text through scalar SymbolTable readers. The scalar API avoids a struct-Option crossing but does not itself preserve the text allocation across HIR scope end. The actual retaining/promoting owner is unlocalized, so solution and structural scope stay unknown.

## stage2_test_runner_record_collection_owner_unavailable_2026_10_12 — Stage2 test runner cannot rebind exact record collection provider

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn:80; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn:2389; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:1002; frozen input/open_bugs_08.tsv exact ID row
```
- Review rationale: The frozen record is a command/compact GH3298 description, not a report. Exact-target searches locate the same database entry, not a retained diagnostic naming the failing owner. Independently inspected rebind_record_element_owner: enum sentinel, missing owner and generic arguments have explicit pass-through branches; an exact Named-owner rebind error still emits provider/consumer/symbol/span evidence. This establishes the consumer, but not which branch the historical record exercised or whether its guard reflected a producer bug. Accepted conservative uncertainty after bounded source/successor investigation.
- Review corrections: Downgrade valid to uncertain: no exact failing owner key or GH3298 receipt was recovered; current guard alone does not validate the specific historical failure.

## stage2_unwrap_on_array_pop_yields_nil_2026-09-13 — BUG: `.unwrap()` on an `Array.pop()` result yields nil in the seed's LLVM native lane

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_unwrap_on_array_pop_yields_nil_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:4998; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:6515; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/parallel.spl:297
```
- Review rationale: Report's historical LLVM pop returns a raw tuple while unwrap extracts an enum payload; it separately measures double evaluation of pop under ??. Current Simple unresolved-array lowering obtains Option via first/last before raw pop mutation, while bootstrap DFS uses index/slice. Those lane-specific paths cannot establish a coordinated seed LLVM/Cranelift/optional ABI repair. Keep unknown and explicitly avoid treating the DFS bypass as a root fix.

## stage2_windows_msvc_struct_receiver_probe_segv_2026-09-01 — Windows MSVC Stage 2: struct-receiver capability probe SEGVs (new, distinct from the resolved module-init bug)

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage2_windows_msvc_struct_receiver_probe_segv_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-bootstrap-stage2-struct-receiver.shs:68; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/linker.rs:2337
```
- Review rationale: Full report's reduction and disassembly establish CRT startup calling RVA0 after unresolved-symbol suppression, not receiver ABI damage. Current gate sets SIMPLE_NO_STUB_FALLBACK=1 for both probes and derives MSVC flavor from target. The inspected linker branch permits duplicate definitions only, explicitly excluding UNRESOLVED suppression. A strict-link correction addresses this gate's measured A/B failure; a current Windows artifact and separate positional-route successor remain unqualified.
- Review corrections: frozen queue solution: unknown -> known; frozen queue structural_change: unknown -> no; frozen queue recommended_action: keep_open -> fixed_pending_verification

## stage3_attempt_clobbers_admission_env_breaking_next_receipt_2026-09-02 — Every Stage-3 attempt clobbers `admission.env`, breaking the NEXT receipt producer

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_attempt_clobbers_admission_env_breaking_next_receipt_2026-09-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:174; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:3795; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:4804
```
- Review rationale: Read full report, including misleading normalization heading: its resolved scope note confirms the writer census, not the clobber defect. Current receipt producer still verifies admission.env against both parent digests; current publication seals the directory and writes parents in the trust-root branch. This inspected path does not establish safe repeated-attempt lifecycle/reuse across every branch. Keep open with unknown repair, preserving the integrity check.

## stage3_bootstrap_closure_mir_lowering_retention_2026_10_20 — Stage 3 bootstrap-fixed closure MIR lowering retains ~36 MB per module (13 GB -> 53 GB over 1100 modules)

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_bootstrap_closure_mir_lowering_retention_2026_10_20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_pipeline_lowering.spl:1182; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2265; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLowering/module_lowering.spl:2385
```
- Review rationale: The report contrasts an unscoped closure loop retaining about36MB/module with transient direct lowering. Current driver calls lower_bootstrap_closure_module, which routes through scoped lowering and fails closed on returned errors. Scoped owner clears consumer scratch, promotes returned MIR and explicit persistent owners/registries, ends the scope, restores borrowed providers and publishes reverse references. This is an ownership/lifetime-boundary remedy, not a measured memory bound. Current source-matched retained-heap/RSS qualification is still required.
- Review corrections: frozen queue solution: unknown -> known; frozen queue structural_change: unknown -> yes; frozen queue recommended_action: keep_open -> fixed_pending_verification; Set structural_change=yes: remedy changes per-module allocation ownership, escape-set promotion and cross-module lifetime boundaries; it is more than a local arithmetic/branch correction.

## stage3_closure_omits_definition_owner_modules_2026-09-01 — Stage 3: the entry closure omits definition-owner modules, so 764 of 1064 hir-fatals are "unresolved type" for types whose owner was never loaded

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_closure_omits_definition_owner_modules_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_entry_closure_core.spl:621; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_entry_closure_core.spl:703
```
- Review rationale: Full report retracts wrong-file and load/prune theories: character-indexed newline scanning was mixed with byte slicing after an em dash. Current extracted _driver_line_end advances byte_at offsets, and the import walker consumes those indices and advances line_start consistently. The report historically recovered hir_operators and removed its436 fatals, while910 other type messages and canonical native-build qualification remained. This supports a bounded newline-unit correction only.
- Review corrections: frozen queue solution: unknown -> known; frozen queue structural_change: unknown -> no; frozen queue recommended_action: keep_open -> fixed_pending_verification

## stage3_current_source_hir_rss_termination_2026-08-14 — Current-source Stage 3 terminates at status 143 after unbounded HIR-build RSS growth with

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/driver/stage3_hir_lowerer_reuse_contract_spec.spl:19; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c:3250
```
- Review rationale: Research used the queue's spec locator instead of recovering the available75KB canonical report. I read its initial owner/reset history, later diagnostic corrections and final registry-churn evidence. The report withdraws broad scope-widening as a root fix and leaves promotion closure/unowned allocation attribution open; churn repair reduces bookkeeping buffers only. Current runtime promotion has ownership classification and graph planning, and streaming source contracts do not prove RSS boundedness. Retain unknown/open; no canonical Stage3 measurement is available.
- Review corrections: Correct missing-report claim: canonical report exists at doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md. Source/spec contracts cannot substitute for its corrected memory-attribution evidence.

## stage3_driver_hir_lowering_spins_after_parse_fix_2026-09-21 — Stage 3 makes no observable progress in driver HIR lowering once the parse phase passes

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_driver_hir_lowering_spins_after_parse_fix_2026-09-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_build.spl:320; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_import_resolution.spl:308
```
- Review rationale: Full report retracts definitive spin language: log/RSS stayed flat while CPU advanced, but later RSS dropped5GB, and the process was killed rather than observed never to terminate. Current HIR import phase brackets resolve_import_symbols and package-sibling resolution; resolve_import_symbols enters resolve_import_list. This locates a broad phase, not a failing operation. Keep a valid historical progress/performance defect with unknown root and untested current behavior.

## stage3_f030_final_parse_marker_rss_growth_2026-08-08 — Stage 3 self-host at f030 stalls after its final parser-progress marker while RSS grows

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_f030_final_parse_marker_rss_growth_2026-08-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_source_pipeline_parsing.spl:1059; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_orchestration.spl:509
```
- Review rationale: The report is one externally terminated observation: RSS grew after a final parser marker, without a stack. Current parse_all_impl still separates entry-closure work from the orchestration HIR-start marker. The last filename therefore cannot identify the allocator or prove parser/AST retention. Keep unknown/open; meaningful attribution needs a retained phase/heap trace rather than another unchanged full replay.

## stage3_hir_enum_payload_closure_stack_overflow_driver_2026-09-14 — Stage 3 SEGV: the HIR enum-payload closure recurses the main stack to death on `compiler.driver.driver` (2026-09-14)

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_hir_enum_payload_closure_stack_overflow_driver_2026-09-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:578; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/context_helpers.spl:54
```
- Review rationale: Full report's later correction retracts its Dict-underreporting proof: the identity ceiling and declaring-owner stability were unverified. Current wrapper forms an input-tuple key, checks a linear in-progress array, pushes before recursive materialization and pops afterward; accessors implement that lifecycle. This is a concrete recursion bound, but the source comment still repeats the retracted mechanism and the report explicitly calls the bound not an explanation. No root producer repair or canonical macOS qualification is established.
- Review corrections: V2 research solution: known -> unknown; V2 research structural_change: yes -> unknown; V2 research recommended_action: fixed_pending_verification -> keep_open; Reject research known/yes/fixed_pending_verification as a whole-root claim. Guard is a present mitigation; report correction leaves lookup versus identity proliferation unresolved. Also reject stale source comment as proof of Dict under-reporting.

## stage3_hir_segv_compiler_driver_unit2of833_2026-09-14 — Stage 3 native-build SEGVs in the HIR phase at unit 2 of 833 (`compiler.driver.driver*`)

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_hir_segv_compiler_driver_unit2of833_2026-09-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:578; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_build.spl:320
```
- Review rationale: Read all chronology: initial unit2 crash, later three crashes at different HIR imports, then an unrun hypothesis connecting macOS crashes to Linux40GB plateau. Neither a depth cap in one reexport walker nor memory-capacity arithmetic identifies these faults or rules out all other recursion. The adjacent current payload reentry guard is not a demonstrated fix for this record. Retain valid historical crashes, unknown remedy and separate current qualification.

## stage3_links_stale_rust_runtime_archive_runtime_fixes_are_noops_2026-08-17 — Stage 3 links a STALE Rust runtime archive — every runtime-side fix is a silent no-op there

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_links_stale_rust_runtime_archive_runtime_fixes_are_noops_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:3066
```
- Review rationale: The report proves the old archive mismatch through rt_clear disassembly and distinguishes source/mtime from linked bytes. Current bootstrap still detects stale seed/runtime stamps and only warns/reuses for a non-full flow, while full bootstrap selects a content-fingerprinted authority root. That reachable policy preserves a freshness risk, but an exact current linked archive has not been checked and full admission lifecycle impact of a repair is not established. Keep unknown/open.
- Review corrections: V2 research structural_change: no -> unknown; Downgrade research structural_change=no to unknown: warning branch is located, but no complete authority/admission lifecycle repair is demonstrated.

## stage3_macos_full_graph_hir_sigsegv_2026_09_21 — macOS Stage3 full-graph HIR crashes with SIGSEGV after 104 of 848 modules

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn:147; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn:5189; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn:5257; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_build.spl:320; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/process_governor.spl:11
```
- Review rationale: No same-ID report was found; exact-target DB evidence contains candidate/receipt/log hashes,104/848 progress and signal139, bounded peak memory, and a focused process_governor success. Current import phase and process_governor imports were inspected; they show the in-flight context, not a fault owner. Historical evidence supports validity, while a crash IP or reproducing full-graph reduction is still missing. Keep open; do not infer OOM, process-governor failure or BOOT20 equivalence.

## stage3_mir_runtime_error_trace_segv_2026-08-15 — Stage 3 MIR lowering SIGSEGV after RuntimeError call trace

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_mir_runtime_error_trace_segv_2026-08-15.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:6117
```
- Review rationale: Full report explicitly says RuntimeError was the last successful trace, with no retained core/IP. Current MethodCall arm emits before/after markers around lower_method_call and returns the resulting local; a completed after marker cannot locate the subsequent SIGSEGV. No source correction or root cause is supported. Preserve valid historical MIR crash and unknown/open classification.

## stage3_mir_values_equal_segv_after_full_hir_2026-08-25 — Stage 3 self-host SIGSEGV while lowering `values_equal` after full HIR

- Source receipt: `adjudication_v2_25`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_mir_values_equal_segv_after_full_hir_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:7423; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:7557; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3899
```
- Review rationale: Report shows successive source bypasses clearing values_equal then eval_gt, followed by eval_gteq failure; final cycle stopped before MIR. Current direct enum-only route uses original typed HirMatchArm reads before normalization, and enum-body copies are absent; mixed-pattern normalization still exists. These consumer-shape changes do not repair general ANY-backed composite transport, nor qualify the final nested-enum frontier. Keep the broader tracked carrier defect open with unknown root remedy.
- Review corrections: V2 research solution: known -> unknown; V2 research structural_change: no -> unknown; V2 research recommended_action: fixed_pending_verification -> keep_open; Downgrade research known/no/fixed_pending_verification: source bypasses removed earlier crash frontiers but report explicitly retains general carrier defect and unverified eval_gteq. Add actual enum-lowering owner instead of inferring it from absence of enum_bodies.

## stage3_native_build_and_compile_segv_on_hello_world_2026-08-18 — bootstrap/stage3/simple SEGVs on both of its two commands (hello world)

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md:14-53,213-251,255-278,320-343; doc/08_tracking/bug/c_runtime_missing_83_codegen_runtime_symbols_2026-08-21.md:8-13; scripts/bootstrap/bootstrap-from-scratch.sh:5423-5434,5632-5638,5906-5916; frozen queues_v2/group26.csv; 
```
- Review rationale: Independently checked the report's original blob, Aug 31 replacement disclaimer and Sept 14 changed failures, plus triple-scoped bootstrap output/sanity selection. Retain valid historical crash, unknown remedy; output routing alone does not establish deployment lineage.
- Review corrections: No raw category change proposed. Historical failure remains valid; later unlike failure is not proof of repair or falsity.

## stage3_native_build_segv_generic_codegen_link_path_2026-08-06 — Self-hosted stage3 SIGSEGVs in SymbolTable.lookup on essentially every native-build

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md:1019-1056,1080-1087,1091-1139; test/01_unit/compiler/mir/struct_field_order_module_qualified_spec.spl:16-29,115-124; src/compiler/50.mir/_MirLowering/function_lowering.spl:1754-1824; frozen queues_v2/group26.csv; 
```
- Review rationale: Original report lines 43-79 contain a concrete NULL scope-load backtrace, whereas the later call-zero explanation is not reconciled with that nonzero-PC instruction. Current resolve_field_index has value-provenance and module-qualified tiers, but these do not identify the original generic-call fault. Historical crash remains valid; root attribution remains unresolved.
- Review corrections: Restore valid historical symptom: lack of proof that the field-index fix caused the crash does not negate the original direct crash evidence. Retain the explicit NULL-load versus later call-zero attribution conflict.

## stage3_native_build_serial_ignores_jobs_2026-09-14 — Stage-3 bootstrap native-build ignores --jobs/--threads: measured single-core at real 14,340-file scale (2026-09-14)

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_native_build_serial_ignores_jobs_2026-09-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_native_build_serial_ignores_jobs_2026-09-14.md:7-45,47-87,95-123; src/compiler/80.driver/driver_build/parallel.spl:450-458,469-477,533-545; src/compiler/80.driver/driver_aot_native_output.spl:2683-2726; frozen queues_v2/group26.csv; 
```
- Review rationale: Independently checked build's sequential fallback and AOT's in-process capsule caller. Report demonstrates historical single-thread sampling, not all-phase timing. The sibling huffman report corrects the same run's claimed 14,340 closure to 832; 14,340 counts broad roots, so do not retain the 14k closure extrapolation.
- Review corrections: Correct research's real-14,340-file framing using sibling report's explicit same-candidate correction: final closure was 832. Structural ownership boundary remains supported; performance is untested.

## stage3_nil_coalesce_owner_enum_handle_stale_runtime_2026-08-17 — Stage 3 trace showed `??` on `text?` yielding `<enum@0x...>` — not reproducible from the current tree

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_nil_coalesce_owner_enum_handle_stale_runtime_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_nil_coalesce_owner_enum_handle_stale_runtime_2026-08-17.md:7-19,21-63; src/runtime/runtime_native.c:6062-6069; src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:478-515; frozen queues_v2/group26.csv; 
```
- Review rationale: Report retains 62 enum-handle owner trace lines; current rt_unwrap_or_self gates canonical Option, and moved trace reads symbol.defining_module after a table predicate. Stale archive and stale symbol identity remain competing explanations. They limit cause diagnosis rather than negate the observed symptom.
- Review corrections: Restore valid historical observation; unknown stale-runtime/stale-id cause is not sufficient to downgrade symptom validity.

## stage3_no_gc_parse_hir_retention_2026-08-25 — Stage 3 no-GC parse/HIR retention exceeds bootstrap memory budget

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_no_gc_parse_hir_retention_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_no_gc_parse_hir_retention_2026-08-25.md:18-71,90-115,117-138; src/compiler/80.driver/driver_source_pipeline_parsing.spl:1464-1489,1536-1544; src/compiler/80.driver/driver_hir_pipeline_lowering.spl:1648-1662,1702-1710; frozen queues_v2/group26.csv; 
```
- Review rationale: Plain parse still retains ParserModules and layer-wiring arrays. Streaming HIR has source reclamation and owner eviction, but no source proof that the reported full no-GC graph is safely bounded. The report's Cycle15 tail crash is separate from its measured memory growth; retain unknown root remedy.
- Review corrections: No raw category change proposed.

## stage3_phase2_surface_stall_after_huffman_46gb_2026-09-14 — Linux S3-1: Stage-2-native `bootstrap_main.spl` build hangs after the surface phase completes — seed interpreter finishes the identical closure in 17 minutes

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_phase2_surface_stall_after_huffman_46gb_2026-09-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_phase2_surface_stall_after_huffman_46gb_2026-09-14.md:24-36,38-59,61-82,199-267,268-312; src/compiler/20.hir/hir_lowering/module_surface_registry.spl:502-520,580-640; src/compiler_rust/runtime/src/value/collections.rs:96-115,168-185,3081-3120,3186-3218,3255-3269; frozen queues_v2/group26.csv; history: c0b3ad911f4cb00c0f3550b05baa8d06347d17d0 ancestry 627440328c2, 7cfa794e2c2
```
- Review rationale: Confirmed batching at module_surface_promote_fields and Rust indexed/tombstoned promotion with deferred ambiguous compaction. This directly addresses the retain cost named by both historical GDB stacks; retain source fix pending native bundle qualification. Data-model restructuring is supported by TransientHeapScope index/membership changes.
- Review corrections: Propose solution unknown -> known, structural unknown -> yes, action keep_open -> fixed_pending_verification. Preserve untested: no current native bootstrap execution.

## stage3_post_file_copy_exit139_2026-08-14 — Stage 3 exits 139 in MirLowering.remember_local_hir_type via maybe_copy_array_value after

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_post_file_copy_exit139_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_post_file_copy_exit139_2026-08-14.md:21-56,58-66; src/compiler/50.mir/mir_lowering_types.spl:958-1018; src/compiler/50.mir/mir_lowering_stmts.spl:740-785,919-925; src/compiler/50.mir/_MirLowering/function_lowering.spl:1163-1169; frozen queues_v2/group26.csv; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0 ancestry a906e4717fb; src/compiler/50.mir/mir_lowering_types.spl:979; src/compiler/50.mir/mir_lowering_stmts.spl:924
```
- Review rationale: Symbolized report names remember_local_hir_type from maybe_copy_array_value and focused scalar-copy qualification. Independently confirmed scalar IDs enter copy_local_hir_type_metadata, which guards missing/nil metadata and copies inside aligned arrays; the array caller uses it. Present bounded repair supports fixed_pending_verification, not current reproduction.
- Review corrections: No raw category change proposed.

## stage3_post_folded_const_diagnostics_sigsegv_2026_08_14 — Stage 3 peaks near 7.7 GiB RSS and exits 139 right after post-folded-constant

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_post_folded_const_diagnostics_sigsegv_2026_08_14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_post_folded_const_diagnostics_sigsegv_2026_08_14.md:8-41,43-82,84-154; src/compiler/50.mir/_MirLowering/asm_and_targets.spl:336-349; src/compiler/50.mir/_MirLowering/bootstrap_globals.spl:41-54,483-490,1068-1080; src/compiler/80.driver/driver_aot_native_output.spl:2716-2726; frozen queues_v2/group26.csv; 
```
- Review rationale: The original pinned admitted-Stage2 run's 0-to-98 diagnostic count and rc139 remain credible historical failure evidence. The later call-zero fixture uses a different 3,464,072-byte Stage3 artifact and does not establish that all three reports are one mechanism. Current fatal flags and bootstrap rejection gates are real, but no complete owner trace connects this original crash to them; keep root remedy unknown.
- Review corrections: Restore valid historical failure; reject W6's cross-artifact family collapse as proven causation. Source error guards do not qualify a fixed outcome.

## stage3_post_parse_surface_window_has_no_receipts_2026-08-17 — Stage 3: the post-parse module-surface window emits no progress receipts

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_post_parse_surface_window_has_no_receipts_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_post_parse_surface_window_has_no_receipts_2026-08-17.md:7-18,47-90,92-110; src/compiler/80.driver/driver_source_pipeline_parsing.spl:1254-1355; frozen queues_v2/group26.csv; 
```
- Review rationale: Current surface-building caller emits receipts before/after per-source building, aliasing, export resolution and finish_into. This remedies the visibility portion of the report, while its explicit 30-minute cost remains undiagnosed. Keep open with unknown whole-report solution; preserve guard hypothesis as unproven rather than using heap-growth rate to prove allocation cost.
- Review corrections: No raw category change proposed.

## stage3_quadratic_transient_heap_promote_2026-09-02 — Stage 3 stalls in `rt_transient_heap_promote` — one enormous scan, NOT quadratic

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_quadratic_transient_heap_promote_2026-09-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_quadratic_transient_heap_promote_2026-09-02.md:7-37,39-78,85-117; src/compiler_rust/runtime/src/value/collections.rs:96-115,168-185,3081-3120,3255-3269; src/compiler/20.hir/hir_lowering/module_surface_registry.spl:630-640; frozen queues_v2/group26.csv; 
```
- Review rationale: The report explicitly retracts per-surface quadratic attribution and admits unknown scope size and scan/drop cost. Current Rust promotion uses indexed release and deferred compaction; current Simple registry now invokes two batched promotions per surface plus root promotion, so current call count cannot reconstruct the historical single-call artifact. Accept uncertain defect classification, unknown remedy for this particular measured stall.
- Review corrections: Do not reuse the later 832-surface case's known root as proof of this earlier 760-module single-call case. A current optimization is not proof that the historical expensive scan was defective.

## stage3_scv_inventory_noncanonical_2026_09_20 — Stage 3 SCV source inventory is noncanonical on admitted FreeBSD Stage 2 compiler

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_scv_inventory_noncanonical_and_stage2_struct_push_segv_2026-09-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_scv_inventory_noncanonical_and_stage2_struct_push_segv_2026-09-20.md:7-20,53-78,85-114; src/lib/scv/compile_source_inventory_core.spl:390-434,398-434; src/lib/scv/compile_source_inventory.spl:441-475; frozen queues_v2/group26.csv; 
```
- Review rationale: Shared report's 16,796/16,802-row native inventories failed canonical readback, and repeat runs differed. Current decoder preserves encode/decode equality guard; successor core uses bytewise comparison and heap sort over struct entries. Neither changed algorithm nor current comparator proves the historical field-read/aliasing producer cause; valid, root remedy unknown.
- Review corrections: No raw category change proposed.

## stage3_scv_inventory_noncanonical_and_stage2_struct_push_segv_2026-09-20 — Stage 3 SCV inventory noncanonical; stage 2 compiler SEGV on struct push

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_scv_inventory_noncanonical_and_stage2_struct_push_segv_2026-09-20.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_scv_inventory_noncanonical_and_stage2_struct_push_segv_2026-09-20.md:7-20,22-52,53-83,85-114; src/lib/scv/compile_source_inventory_core.spl:398-434; src/compiler/50.mir/mir_lowering_stmts.spl:740-785,919-925; frozen queues_v2/group26.csv; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0 ancestry eb975917b8f; no claim that unrelated NamedVar history repairs this push fixture.
```
- Review rationale: Combined report explicitly separates struct-push crash from inventory nondeterminism after PR1144/rebuild. Target history contains merge eb975917b8f, but the array-copy metadata helper cited in research is not a push repair trace. Independently checked current sort and decoder; whole-report remedy remains unknown because the admission-producing inventory defect remains unresolved.
- Review corrections: Propose solution known -> unknown for the combined currently open record: PR #1144 addresses the historical struct-push repro only, while the extant inventory defect remains causally unresolved. Do not treat duplicate/combined registration as invalid.

## stage3_selfhost_exit_139_2026-08-14 — Fresh pure-Simple Stage 2 segfaults (exit 139) while compiling Stage 3 before writing any

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_selfhost_exit_139_2026-08-14.md:18-34,329-360,363-415; src/compiler/20.hir/hir_lowering/module_surface_registry.spl:319-379; src/compiler/80.driver/driver_source_pipeline_parsing.spl:1345-1356; frozen queues_v2/group26.csv; 
```
- Review rationale: Original exit139 console was not retained; report explicitly forbids borrowing sibling run evidence. The later macOS null Result payload is a separately retained observation. Current finish_into uses a caller-created registry and scalar status; from_parts wraps original owner rather than the returned payload. This supports a later scoped remedy, not diagnosis of original crash, so uncertain/unknown remains appropriate.
- Review corrections: Downgrade structural yes to unknown for the original unretained incident; later owner-boundary changes do not prove that original root required restructuring.

## stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05 — Stage 3 self-host dies at exit 139 with the bare leaf 'bytes' hijacked to

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: doc/08_tracking/bug/stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md:7-42,144-185,230-276; src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:4112-4128,4185-4223; src/compiler/50.mir/mir_lowering_stmts.spl:1042-1079; doc/08_tracking/bug/bug_db.sdn:1207; frozen queues_v2/group26.csv; 
```
- Review rationale: Report's historical nil-receiver diagnostic and SIGILL follow the final lower_expr span receipt. Current wrapper guards nil LocalId and statement caller now probes before/after; neither establishes which later consumer faulted. Binding collision hypothesis has explicit counter-evidence and no qualifying experiment. Retain valid failure, unknown root and structure; no fix claimed.
- Review corrections: Restore valid historical failure; uncertainty in producer/caller attribution concerns diagnosis. Avoid claiming that a final receipt proves the exact subsequent fault site.

## stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10 — Indexing self.ctx.errors right after self.ctx = returned struct emits no output natively

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Historical report sections 7-35, 135-174, 193-259, 271-326; source driver_types.spl:1235-1258 and driver_orchestration.spl:540-555,590-604.; frozen queues_v2/group26.csv; src/compiler/80.driver/driver_types.spl:1245; src/compiler/80.driver/driver_orchestration.spl:548,596; doc/08_tracking/bug/stage3_selfhost_phase3_error_array_index_after_struct_reassign_silently_noops_2026-08-10.md:135,271
```
- Review rationale: Report narrows missing diagnostics to text-parameter use yet later returns to reassignment speculation; passing seed controls are explicitly the wrong lane. Current error_message_at guards heap formation and bounds, and orchestration uses it for diagnostic reads. This is containment, not an identified backend root repair. Accept valid historical missing-output defect with unknown solution/structure.
- Review corrections: none identified

## stage3_selfhost_post_hir_segfault_2026-08-14 — Stage3 crashes after HIR: CompileContext.error_count() from lower_and_check_impl segfaults

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 20-52,347-381,498-565; test/02_integration/compiler/stage3_aggregate_receiver_spec.spl:15-36; HIR pipeline source around 1431-1437.; frozen queues_v2/group26.csv; src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1578,4662; doc/08_tracking/bug/stage3_selfhost_post_hir_segfault_2026-08-14.md:498,550
```
- Review rationale: Report separates impossible receiver frontier, subsequent external SIGTERM, and final repeated rc139 after frontend errors; they are not one proved root. Current unresolved push lowers/boxes the argument, emits rt_array_push, writes back and returns receiver. Integration spec asserts scalar consistency and aggregate contents, not native crash absence. Accept historical failure with unknown root remedy.
- Review corrections: none identified

## stage3_selfhost_status_after_dedent_fix_2026-08-10 — Stage-3 self-host status after `ee89798a19f` (parse_module_body Dedent absorb)

- Source receipt: `adjudication_v2_26`; inspection `report_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_status_after_dedent_fix_2026-08-10.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-8,39-50,66-130.; frozen queues_v2/group26.csv; doc/08_tracking/bug/stage3_selfhost_status_after_dedent_fix_2026-08-10.md:46,88,99
```
- Review rationale: Read full interrupted-run handoff: after Dedent change the run reached 52.5GB and exit143 with no error line or candidate; it used four threads instead of recorded two. This is neither a successful Dedent verification nor a demonstrated remaining compiler defect. Accept uncertain/unknown tracker classification; exact admitted after-state is still absent.
- Review corrections: none identified

## stage3_selfhost_symbol_alias_conflict_2026-08-04 — Stage-3 self-host: `Symbol` struct/type_alias conflict and nil-receiver crash

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_symbol_alias_conflict_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-6,50-88,109-154; src/compiler/90.tools/query_types.spl:61; src/compiler/00.common/effects.spl:29; related lower_expr nil-receiver report.; frozen queues_v2/group26.csv; src/compiler/90.tools/query_api.spl:136,149; src/compiler/90.tools/query_types.spl:61; src/compiler/00.common/effects.spl:29; doc/08_tracking/bug/stage3_selfhost_symbol_alias_conflict_2026-08-04.md:109
```
- Review rationale: Report records two distinct failures, partial QuerySymbol renaming, and a separate nil-receiver crash. Current query type declarations and actual query API signatures use QuerySymbol/QuerySymbolV2, while effects retains module-local Symbol=text. This confirms the narrow collision avoidance, not a repaired global registry identity contract or the nil crash; whole-record root remedy remains unknown.
- Review corrections: none identified

## stage3_selfhost_unresolved_builtin_types_2026-08-31 — CORRECTION 2026-08-31 — this record's original framing was WRONG

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_unresolved_builtin_types_2026-08-31.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report correction and root analysis sections 1-24, 154-205; driver_source_pipeline_loading.spl:1020-1042; history at assessed SHA includes 6f53cfa8cd4 and adjacent loader changes.; frozen queues_v2/group26.csv; src/compiler/80.driver/driver_source_pipeline_loading.spl:1023,1121,1143; doc/08_tracking/bug/stage3_selfhost_unresolved_builtin_types_2026-08-31.md:24,154
```
- Review rationale: Read correction and both roots: builtin advisory counts were not fatal; missing physical providers and glob visibility remain historical defects. Current closure seeds loaded names/paths only from all_sources, resolves each importer-relative source, and validates selected versus loaded physical owner before proceeding. This differs from the alleged bare membership skip, but does not prove all original missing providers/glob failures repaired; retain unknown whole-record solution.
- Review corrections: none identified

## stage3_selfhost_vtable_field_offset_relro_segv_2026-08-06 — Cross-module field read on vtable-bearing class uses wrong offset and writes into RELRO

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_vtable_field_offset_relro_segv_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-6,82-123,147-174; driver_bootstrap.spl:364-370; native_project/compiler.rs:1707 named in report; git history for driver_bootstrap at assessed SHA.; frozen queues_v2/group26.csv; src/compiler/80.driver/driver_bootstrap.spl:379,426; src/compiler_rust/compiler/src/pipeline/native_project/compiler.rs:2064-2118
```
- Review rationale: Report's RELRO write instruction, vtable symbol and annotation ablation support a real layout defect. Target direct callers still type translator as MirToLlvm at 379/426; research incorrectly focused only on the helper's inferred local. Rust layout pass still assigns headerless for unresolved or absent owner names at 2100/2118. Annotation is a workaround; a complete root correction must distinguish erased accesses from class ownership, so unknown remedy/structure.
- Review corrections: Reject known/structural-yes from workaround alone. Correct research omission: explicit MirToLlvm locals remain in both actual callers. Later unrelated call-zero artifacts do not refute the original nonzero-PC RELRO write.

## stage3_selfhost_zerokind_compile_specialized_template_release_macos_2026-09-05 — Stage 3 self-host fails: E-MIR-TYPE-ZeroKind on `compile_specialized_template_release` scope-tail (macOS arm64)

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_selfhost_zerokind_compile_specialized_template_release_macos_2026-09-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-5,53-70,120-152; function_lowering.spl around 1354; bootstrap_globals.spl ownership references in report; report says earlier victim patch was not localization.; frozen queues_v2/group26.csv; doc/08_tracking/bug/stage3_selfhost_zerokind_compile_specialized_template_release_macos_2026-09-05.md:84,145,157,200,211; src/compiler/20.hir/hir_lowering/module_surface_registry.spl:565-590
```
- Review rationale: Report addendum retracts pipeline_fn victim and duplicate error count, identifying one entry-module fatal with a stale global scope-tail label. It never identifies the escaping HirType; later repro attempts have no verdict. Current surface promotions explicitly retain composite/callable/import arrays and registry roots, but this does not establish liveness of the unidentified object. Accept valid historical ZeroKind failure, unknown root/structure.
- Review corrections: none identified

## stage3_step_omits_package_index_cold_init_scv_authority_missing_2026-09-13 — Stage 3 cannot start: the canonical Stage-3 step passes no package-index authority and no cold-init

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_step_omits_package_index_cold_init_scv_authority_missing_2026-09-13.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-2,30-70; driver_source_pipeline_loading.spl:365-373,506; bootstrap-from-scratch.sh:4376-4406,5476-5509; commit history at SHA.; frozen queues_v2/group26.csv; scripts/bootstrap/resume-stage3-from-admitted.sh:970-1000,1030; scripts/bootstrap/lib/stage3-native-build-worker.sh:158; scripts/check/lib/bootstrap-stage3-candidate-builder.shs:287,317; scripts/bootstrap/bootstrap-from-scratch.sh:4405,5508
```
- Review rationale: Historical same-candidate A/B isolates absent package-index cold-init. Independently traced all three current launch routes: full bootstrap and candidate builder set it in hash and invocation; resume hashes it and calls stage3-native-build-worker which sets it. Existing loader still rejects missing authority unless cold route is selected. Present bounded env plumbing supports fixed_pending_verification; distinct SCV inventory opt-in remains untouched.
- Review corrections: Change structural yes to no: this is explicit environment propagation within existing admission contracts, not a new ownership/phase architecture. Do not trust normalized Closed heading as qualification.

## stage3_surface_freeze_segv_blocks_mcdc_rt_hal_verification_2026-08-25 — Stage 3 HIR lowering errors block MC/DC/RT-HAL verification

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_surface_freeze_segv_blocks_mcdc_rt_hal_verification_2026-08-25.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-5,87-155, including failed-fix update; current driver_types/error accessor and driver_orchestration caller named in report; chronology in report.; frozen queues_v2/group26.csv; src/compiler/80.driver/driver_types.spl:1245-1257; doc/08_tracking/bug/stage3_surface_freeze_segv_blocks_mcdc_rt_hal_verification_2026-08-25.md:32,87,111
```
- Review rationale: Report first corrects surface_freeze to malformed nested Span in HIR, then records explicit diagnostic progress and a later independent phase2 reporter crash. Its attempted scalar/array length fix failed before printing. Current error_message_at checks array formation before length, but malformed heap content and underlying hidden phase2 error remain undiagnosed. Do not extrapolate a required structural repair from these frontiers.
- Review corrections: Downgrade unsupported structural yes to unknown. Retain separate cleared nested-span/import frontier and later diagnostic-array failure.

## stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06 — SymbolTable.lookup traps ud2 field access on nil receiver during stage3 native-build

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Spec purpose/context and assertions in symbol_table_lookup_scope_guard_spec.spl:7-39,135-168; hir_symbol_table_methods.spl:122,194; hir_types.spl:453,657; prior/revert commits 1ea6599e8fb and 030ff43e330 from spec.; frozen queues_v2/group26.csv; src/compiler/20.hir/hir_symbol_table_methods.spl:164,205; src/compiler/20.hir/hir_types.spl:640,646,657; doc/08_tracking/bug/stage3_symboltable_lookup_ud2_field_access_nil_receiver_2026-08-06.md:302-433
```
- Review rationale: Read full provenance correction: missing guard reflected the binary's real source, not codegen deleting it. Current lookup/lookup_or_invalid range-check scope IDs; declare/pop recover to root, and push inserts before increment. These prevent out-of-range reads, but report itself says flat MIR table should always use valid root and never establishes actual corrupt scope ID. Interpreter guard specs therefore do not identify or repair the original native cause.
- Review corrections: Reject known/structural-yes/fixed_pending_verification for original crash: safe range guards are supported containment, while the report's three root candidates remain unresolved.

## stage3_unresolved_call_warning_family_2026-08-07 — run_check unresolved because Rust seed source collector hardcodes a *check.spl exclusion

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_unresolved_call_warning_family_2026-08-07.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-5 and especially 2b lines 220-317; src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:2657 and collector caller discovery.rs:824; app/cli/check.spl and its run_check callers.; frozen queues_v2/group26.csv; src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:2657-2676; src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs:820-835; doc/08_tracking/bug/stage3_unresolved_call_warning_family_2026-08-07.md:220-328
```
- Review rationale: Mechanism C's historical filename discriminator is concrete, but current collect_spl_files_recursive includes every regular .spl file with no check.spl substring filter; discovery full scan calls that owner. Research's source listing does not support a still-present exclusion. This narrow old cause appears removed, while the report includes other unresolved family mechanisms; whole-record solution stays unknown, open.
- Review corrections: Reject known/no for the entire family and any implied current check.spl exclusion. Current owner explicitly lacks that branch; do not duplicate its removal or infer family closure.

## stage3_worker_reaped_silently_in_hir_typecheck_2026-09-05 — Stage-3 worker dies silently in phase 3, and it is NOT an OOM

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage3_worker_reaped_silently_in_hir_typecheck_2026-09-05.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/native_build_main.spl:2182-2213; scripts/bootstrap/bootstrap-from-scratch.sh:5683; doc/08_tracking/bug/stage3_worker_reaped_silently_in_hir_typecheck_2026-09-05.md:110,254,423,518
```
- Review rationale: Report's UPDATE2 apport entries identify signal11 against stage2-admitted worker; later seed fmt core and monitor kills are expressly different artifacts/populations. Current native-build wrapper recognizes core-dump text with -1, distinguishes signal statuses, and bootstrap255 warning avoids claiming a kill. Diagnostics improve attribution but do not diagnose the post-HIR fault; accept valid historical crash with unknown root.
- Review corrections: Restore valid historical signal11 population despite unrelated retained fmt-core provenance. Remove nonexistent bootstrap-session-exec.c reference as decisive owner evidence.

## stage4_bootstrap_receipt_planner_unavailable_2026-08-15 — Stage 4 bootstrap receipt planner unavailable

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_bootstrap_receipt_planner_unavailable_2026-08-15.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Full report lines 1-36, especially captured binary identities, rc139, Stage-3 unknown-command result, and explicit recovery exception; report calls for runtime/dispatcher owner reproduction.; frozen queues_v2/group26.csv; src/app/build/bootstrap_receipt_main.spl:7; src/app/build/bootstrap_receipt_planner.spl:63-98; doc/08_tracking/bug/stage4_bootstrap_receipt_planner_unavailable_2026-08-15.md:18-35
```
- Review rationale: Historical full CLI crashed in both compiled and source-run planners; bootstrap-only Stage3 rejected build. Current minimal receipt entry calls plan_bootstrap_authorization, which checks typed reason and four admission hashes before writing v2 receipt. This is a relevant successor path but does not identify the original runtime/dispatcher crash. Accept valid unavailable planner, unknown remedy; preserve admission policy and do not treat recovery exception as repair.
- Review corrections: none identified

## stage4_cli_entry_closure_resolver_probe_unverified_2026-07-26 — Stage 4 CLI entry-closure resolver candidate remains unverified without a manifest-attested full CLI

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_cli_entry_closure_resolver_probe_unverified_2026-07-26.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-5, especially 13-82 and required experiment 82-109; compile_targets.spl:29,1571; native_build_closure.spl closure owner; source history at assessed SHA.; frozen queues_v2/group26.csv; src/app/io/_CliCompile/compile_targets.spl:1571; src/app/io/_CliCompile/native_build_closure.spl:339-401; doc/08_tracking/bug/stage4_cli_entry_closure_resolver_probe_unverified_2026-07-26.md:13-30
```
- Review rationale: Full report calls 10s/30s figures unverified and lacks the command/hash/log. Current caller routes to native_build_closure: it deduplicates physical keys, normalizes roots once, and caches resolution per importer directory plus spelling. This materially differs from old hot-path description, but proves no performance outcome or needed architectural change. Accept uncertain candidate, unknown remedy/structure.
- Review corrections: Downgrade structural yes to unknown. Correct stale hot-path inference: current code has physical-key dedup and per-directory resolution cache; historical scheduling figures remain unqualified.

## stage4_deploy_timeout_blocks_release_path_guard_2026-07-08 — stage4 deploy timeout blocks direct release-path guard

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_deploy_timeout_blocks_release_path_guard_2026-07-08.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-7; cli_ops.spl:307-330 and callers 368,387; report deployment attempts and explicit uncompleted artifact requirement.; frozen queues_v2/group26.csv; src/app/io/cli_ops.spl:249-293,307-321,351-393; doc/08_tracking/bug/stage4_deploy_timeout_blocks_release_path_guard_2026-07-08.md:36-69
```
- Review rationale: Report distinguishes direct release-path failure from two unfinished Stage4 deploys. Current self-exec identity comes from in-process /proc/self/exe resolution with fallbacks, and candidate symlinks are compared before explicit delegation. That is a present guard improvement, not the report's old shell-parent implementation. Why Stage4 timed out and which deployed artifact carries the guard remain unestablished; keep deployment blocker open.
- Review corrections: Reject known/structural-yes/fixed_pending_verification as a diagnosis of the deploy timeout. Guard source alone does not identify a root fix for inability to finish deploy; current implementation is in-process kernel identity, not the historical /proc/$PPID shell helper.

## stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01 — Stage 4 full CLI cannot be linked: 579 codegen-emitted runtime symbols have no definition (2026-09-01)

- Source receipt: `adjudication_v2_26`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0: Report sections 1-6 and full reproduction/result 1-54; stubs.rs:1128-1150; representative runtime names rt_alloc_page_aligned, rt_array_min, rt_cli_dispatch_rust, rt_vulkan_* from report; assessed source tree.; frozen queues_v2/group26.csv; src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:1114-1157; src/compiler_rust/runtime/src/value/collections.rs:7192; src/compiler_rust/runtime/src/value/cli_sffi.rs:148; doc/08_tracking/bug/stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01.md:30-69
```
- Review rationale: Report's 579 count describes one historical link closure, not target-wide absent definitions. Current preflight exempts strict-final-link mode and leaves live missing symbols to the real linker; other non-stub paths reject unresolved runtime names unless explicit bypass. Representative rt_array_min now has implementation, while rt_cli_dispatch_rust merely returns zero. Neither symbol presence nor guard proves a qualified full CLI; provider/closure diagnosis remains unknown.
- Review corrections: Downgrade structural yes to unknown: list size alone does not establish required architecture. Correct research's unconditional preflight claim by noting strict_final_link and stub_missing_runtime branches; no guard weakening proposed.

## stage4_link_undefined_peer_symbols_2026-07-28 — Stage4 full-CLI link: undefined peer-code symbols (link stage reached)

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_link_undefined_peer_symbols_2026-07-28.md#L37-L60; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/office/sheets/access_server.spl#L6-L14; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/office/sheets/calc_access_session_host.spl#L242-L286; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.standalone/__init__.spl#L2; history cae7dbc7188
```
- Review rationale: The full report narrows the unresolved link error to one injected-server call, not all fn-parameter calls. At c0 access_server delegates to calc_access_session_host and that host owns its socket loop, eliminating the original caller. This is relevant changed behavior, but does not diagnose or repair export/call mangling; an obsolete call alone cannot establish a root solution for the tracked compiler/link defect.
- Review corrections: Reject research known/no/fixed_pending_verification: removed caller is not a demonstrated mangler remedy. Current link untested. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## stage4_post_hir_corrupt_module_runaway_2026-08-02 — Stage4 post-HIR pass loops unbounded on a corrupt module instead of aborting

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_post_hir_corrupt_module_runaway_2026-08-02.md#L1-L26; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_lowering.spl#L2228-L2230; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_hir_pipeline_support.spl#L255-L258; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/driver/hir_function_count_spec.spl#L90-L109
```
- Review rationale: The report explicitly retracts corrupt-aggregate attribution: Dict.len caused the negative count. Independently read driver_dict_entry_count (typed keys().len()), its lowering caller before phase_hir_modules storage, and empty/populated/replacement assertions. Those establish the count correction, not the cause or resolution of the observed CPU/RSS runaway. Keep the full historical symptom open with unknown remedy.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## stage4_resume_from_admitted_gap_2026-08-14 — Stage4 cannot continue from an already-admitted resumed Stage 3 artifact

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stage4_resume_from_admitted_gap_2026-08-14.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/resume-stage4-from-admitted.sh:31-172; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:3758-3765; exact-target caller grep scripts/src/test; target-ancestor 6f1269a70d59b621afaf2b533c1e6e90f2a7e496 wrapper diff
```
- Review rationale: The historical report claims a locked planner-bound continuation repair and the helper still implements those checks. However, exact c0 wrapper lines 3758-3760 reject --resume-stage4-from-admitted because it bypasses the admitted Phase2 build manager. Exact-target search finds no production resume_stage4_prepare caller; ancestry-bound commit 6f1269a70d59b621afaf2b533c1e6e90f2a7e496 explicitly removed that call and installed the refusal. Therefore helper/test presence cannot establish a working current continuation. Managed successor continuation remains to be traced/qualified; preserve the admission guard.
- Review corrections: Reject research known/yes/fixed_pending_verification: decisive current caller and history contradict its claimed wired continuation. This is an obsolete source-repair claim, not invalidity and not authorization to bypass the manager. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## stale_snapshot_clobber_4edef8fab8e_2026-08-26 — Stale-snapshot clobber: `4edef8fab8e` ("feat: snapshot current development state")

- Source receipt: `adjudication_v2_27`; inspection `report_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stale_snapshot_clobber_4edef8fab8e_2026-08-26.md#L1-L230; historical refs in report: 4edef8fab8e, parent 993760b729f, baseline 2b35049f8d7, batch commits 26de1a115c3/eccb04c8018e/15fef1d8e406
```
- Review rationale: Read the complete 230-line ledger including corrected 11225-path scale, four repair batches, three entangled clusters and explicit residual uncertainty. The reported 6324 residual paths refer to its historical baseline, not a c0 recount. Dependency-coupled hand merges and unclassified omissions support the historical incident but do not establish a uniform local remedy or structural classification.
- Review corrections: Correct research structural_change=no to unknown; research raw_corrections itself claimed unknown while its field said no. Do not treat historical residual counts as current measurements.

## standalone_hir_lowering_aborts_on_real_compiler_files_2026-08-21 — Standalone parse+lower aborts on real compiler files (`split` on i64)

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/standalone_hir_lowering_aborts_on_real_compiler_files_2026-08-21.md#L1-L61; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/frontend.spl#L369-L375; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_build.spl#L247
```
- Review rationale: Full report identifies split-on-i64, nil enum symbol and missing HirFunction field under the historical seed, with process-per-file containment only. Current parse_full_frontend unwraps its scoped frontend result; lower_module consumes ParserModule, initializes lowering state, and prescans enums before body lowering. These APIs remain relevant, but none of the inspected semantics identifies the three historical carrier failures. Unknown remedy is supported; isolation is not a fix.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## standalone_smf_patternmatch_detector_len_on_i64_2026-08-31 — Standalone native-build of a match-bearing file crashes the unsupported-construct scan with `len` on i64

- Source receipt: `adjudication_v2_27`; inspection `report_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/standalone_smf_patternmatch_detector_len_on_i64_2026-08-31.md#L1-L46; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/compilability.spl#L14-L25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/compilability.spl#L134-L145; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/types.spl#L239
```
- Review rationale: The full report distinguishes a native-build detector len-on-i64 crash from the intentional standalone PatternMatch limitation and correlates receiver value with variant count. Independently inspected CompilabilityAnalyzer's feature-string mapping; it is not the reported variant-list visitor, and the bounded native driver search did not identify that visitor. The historical crash is supported, but active owner and root repair remain unknown.
- Review corrections: Downgrade research source_reviewed to report_reviewed: the feature-list analyzer is not established as the failing scan owner. No known remedy inferred from enum fallback labels.

## starfive_check_deployed_simple_segv_2026-08-15 — Deployed simple check segfaults on StarFive implementation files

- Source receipt: `adjudication_v2_27`; inspection `report_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/starfive_check_deployed_simple_segv_2026-08-15.md:1-43; exact-target git grep copy_local_hir_type_metadata in src/compiler/20.hir returned no match
```
- Review rationale: Located and read the canonical report at c0. It records bin/simple check ramfs.spl exiting 139 before diagnostics using x86_64 executable SHA256 04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0. Later audit says that artifact is absent and separates host redeployment from JH7110 hardware evidence. Its claimed copy_local_hir_type_metadata repair could not be found in current HIR subtree by exact-name search, so no current causal fix is asserted. Historical defect valid, current remedy/structure unknown.
- Review corrections: Resolve low-research unexamined metadata gap: canonical report exists and supplies command/binary identity. Correct uncertain to valid and metadata_only to report_reviewed; do not equate StarFive source paths with a board-runtime crash.

## starfive_dtb_policy_rv64_object_link_2026-08-20 — StarFive DTB policy RV64 freestanding object emission is unavailable

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/starfive_dtb_policy_rv64_object_link_2026-08-20.md#L1-L31; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv64/starfive/boot/starfive_dtb_policy.spl#L38-L79; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/arch/riscv64/starfive/boot/starfive_runtime.c#L32-L58
```
- Review rationale: Read the entire report and actual policy/C call pair. starfive_dtb_policy_select returns candidate or fallback addresses through scalar checks; rt_starfive_resolve_dtb reads candidate/fallback magic and calls that ABI. Hosted success does not establish freestanding RV64 object emission or libc-free linking. The report's minimal projection still failed after bool-cast removal under a source-mismatched compiler, so neither a policy edit nor generic emitter work is an established root remedy.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## starfive_tigard_shifted_tap_ids_2026-08-20 — StarFive Tigard scan intermittently returns shifted TAP IDs

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/starfive_tigard_shifted_tap_ids_2026-08-20.md#L1-L25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/os/starfive-jtag-scan.shs#L11-L27; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/os/lib/starfive-jtag-tap-gate.shs#L4-L10; build/test-artifacts/starfive-jh7110/live-20260820-resume/openocd-sbi-reset-after-clean-scan.log (report ref)
```
- Review rationale: The complete report records shifted IDs and IR errors at two clocks independently of the scanner false positive. The actual shared gate requires exactly two total found TAP records, both expected IDs, and no error markers; scanner self-test contains expected-ID error text as a rejecting fixture. That repairs text acceptance only. No physical cure or current same-log hardware receipt is established.
- Review corrections: Correct research structural_change=no to unknown for the overall physical instability report; a local scanner guard does not classify the undiagnosed hardware cause. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## static_factory_method_chain_wrong_value_2026-08-16 — Chaining a method off a static factory call fails to resolve the method

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/static_factory_method_chain_wrong_value_2026-08-16.md#L1-L74; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl#L184-L200; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl#L410-L420; 99dd520419b9a9a71f82c1973d1783d591521621
```
- Review rationale: The report's Box factory nested inside expect fails under a Rust seed, while val-bound control passes; pure-Simple parity was explicitly unavailable. At c0 declared_static_method_resolution binds an owner symbol and method ID before recursively lowering arguments. This preserves static owner identity but does not by itself show Box.create return-type propagation into the outer double receiver. Unknown root solution remains appropriate; the val workaround is not a fix.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## stats_hangs_after_file_counts_2026-09-02 — `simple stats` prints the file counts and then hangs indefinitely

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stats_hangs_after_file_counts_2026-09-02.md#L1-L67; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/stats_entry.spl#L1-L18; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/stats/dynamic.spl#L340-L366; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/stats/dynamic.spl#L615-L630; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/stats/dynamic.spl#L647-L660
```
- Review rationale: The complete report retains a 41-minute Windows silence after counts and labels doc-coverage attribution a hypothesis. Current dynamic stats calls compute_doc_coverage when non-quick; that owner runs repeated shell grep/find scans. These are a concrete current profiling boundary, not proof of the historic blocked operation. The obsolete-path heading cannot invalidate measured silence. No current profile or known remedy.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## std_gpu_package_import_binds_cuda_externs_to_nocuda_stub_2026-08-25 — `use std.gpu.*` binds `rt_cuda_*` to the no-CUDA stub (device_count 0, cc (0,-3)) while direct module imports see 2 GPUs (2026-08-25)

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/std_gpu_package_import_binds_cuda_externs_to_nocuda_stub_2026-08-25.md#L1-L75; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/gpu_runtime/mod.spl#L24-L48; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/gpu/__init__.spl; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/gpu/mod.spl
```
- Review rationale: Full report later retracts the stub-binding diagnosis and attributes outputs to a foreign build worktree's torch-gated module, with historical strace/sentinel claims. Current nogc_sync_mut gpu_runtime uses rt_cuda_available and rt_cuda_device_count, and package exports now use tiered owners. This supports source evolution but cannot independently bind the historic foreign-tree artifact or prove package dispatch was false. Conservative uncertain/unknown retained; no invalid closure.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: validity: valid -> uncertain; inspection_level: report_reviewed -> source_reviewed.

## std_spec_package_shadows_file_print_summary_2026-07-17 — Bug: `use std.spec.{print_summary, get_exit_code, get_executed_test_count}` — cannot be root-fixed in pure Simple (interpreter mode)

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/std_spec_package_shadows_file_print_summary_2026-07-17.md#L1-L331; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs#L848-L859; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_module/module_loader.rs#L555-L620; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/bdd.rs#L96-L1100; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl#L37-L53; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl#L1655-L1684
```
- Review rationale: Full report includes three independent historical layers and October oversized-file recurrence. At c0 resolver puts project src/lib before vendored root; member import probing preserves unknown instead of converting it to absence. Independently inspected Rust BDD_COUNTS mutations and Simple summary/count functions reading separate module vars. A bridge to the actual interpreter-owned counts is a concrete state-ownership remedy for remaining layers; reexports or path reordering alone cannot provide it. Keep open; no completed wrapper execution.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: solution: unknown -> known; structural_change: unknown -> yes; inspection_level: report_reviewed -> source_reviewed.

## std_suite_failures_are_unbuilt_features_2026-09-20 — Triage: the 9 `test/01_unit/std` failures are unimplemented features, plus one real concurrency defect

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/std_suite_failures_are_unbuilt_features_2026-09-20.md#L1-L71; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/concurrent/thread.spl#L87-L170; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/concurrent/channel.spl#L1-L55; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl#L1100-L1122; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/src/testing/mock/builder.spl#L36-L40; test/01_unit/std/perf_optimization_spec.spl (report’s historical fixture; no current .spl path found)
```
- Review rationale: The report records mixed missing APIs and four concurrency enum-to-int failures, explicitly with unsuccessful isolated reproduction. Current spec owner implements before_all immediate execution and after_all deferred hooks; thread join now returns optional i64 through runtime handle release. These inspected successor semantics refute a blanket current 'all unbuilt' diagnosis but do not locate the four conversion failures. Historical suite report remains valid; a broad tagging change is not an established runtime remedy.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## stdlib_eprint_shadows_prelude_builtin_program_wide_2026-08-17 — `src/lib` defines `fn eprint`, shadowing the prelude builtin program-wide; native-build then cannot resolve `eprint` at all

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stdlib_eprint_shadows_prelude_builtin_program_wide_2026-08-17.md#L1-L305; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_support.spl#L57-L65; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl#L2144-L2148; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/process_ops.spl#L2233-L2242
```
- Review rationale: Read original failure plus rediagnosis and all qualification limits. The stdlib eprint shadow intentionally writes fd2 and must not be renamed. Current is_interp_builtin_fn includes eprint without bootstrap gating, matching the causal missing-HIR-name remedy; MIR returns unit for eprint. Earlier builds timed out or hit RSS before verdict. Concrete bounded repair is present but native fixture/fd2 execution remains untested.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fixed_pending_verification.

## stdlib_spl_edits_not_live_under_bin_simple_run_2026-08-08 — `bin/simple run` resolves `std.*`/`lib.*` to a stale bundled stdlib — on-disk edits are silently ignored

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stdlib_spl_edits_not_live_under_bin_simple_run_2026-08-08.md#L1-L109; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs#L848-L862; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs#L890-L910; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/frontend.spl#L369-L375
```
- Review rationale: The complete report's sabotage-to-7 stayed at the old LCG output under run, while test observed edits; interpreter mode avoided a separate index-shift confound without fixing stale values. Current Rust resolver prefers project src/lib over vendored stdlib in its root loop. This is relevant source hardening, but the report's actual binary file-open origin is not established, so that ordering cannot be promoted to the root cure for this incident.
- Review corrections: Reject research known/no/fixed_pending_verification: a plausible root-order change without historical open-path/binary binding does not establish the causal solution. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## stitch_mcp_file_not_defined_and_missing_auth_2026-09-15 — Stitch MCP: import crash `File is not defined` in Kimi-spawned environments; auth keys absent on this host

- Source receipt: `adjudication_v2_27`; inspection `report_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stitch_mcp_file_not_defined_and_missing_auth_2026-09-15.md#L1-L54; frozen report references .kimi-code/mcp.json and Kimi provider guide
```
- Review rationale: Complete report distinguishes an import-time File ReferenceError in Kimi's foreign-HOME npx cache from expected missing API credentials. Interactive Node v20 reached authentication, while the spawned child executable/package identity was not captured and cache was inaccessible. That evidence supports a real environment discrepancy but cannot establish a current owned-source defect or causal fix. Accepted uncertain/unknown after report review; next step is exact child node/package identity, not credential guessing.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: validity: valid -> uncertain.

## stress_f03_manycall_sum_2026-07-17 — 300-call-chain sum diverges on the interpreter path only; compiled/JIT already correct

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/stress_f03_manycall_sum_2026-07-17.md#L1-L82; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/mod.rs#L690-L730; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/mod.rs#L560-L570; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/builtins.rs#L666-L674; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_eval.rs#L403
```
- Review rationale: Full report reduces interpreter 44786 versus expected 44850 to f64() returning cast-default zero instead of user return 64. Current evaluate_call computes user_defined before builtin execution and builtin_wins_over_user_fn bypasses builtins for user definitions except protected process control names. This directly repairs the reported dispatch-priority cause; no current 300-call or minimal f64 runtime receipt. Known bounded source repair, pending verification.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fixed_pending_verification.

## string_interpolation_silently_evaluates_literal_braces_2026-07-28 — Interpolation evaluates literal brace content with no guard or diagnostic

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/string_interpolation_silently_evaluates_literal_braces_2026-07-28.md#L1-L63; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl#L804-L882; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl#L895-L918; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/70.backend/backend/llvm_ir_builder.spl#L543-L552
```
- Review rationale: Read complete report and current parser region handling plus LLVM emitter. Valid string regions are parsed/interpolated, malformed regions literalized, and doubled braces decoded; llvm.dbg.cu now uses !{{!0}}. That repairs the one caller, while the report intentionally tracks a broader warning for constant-only interpolation. No implemented or accepted warning policy is established, so overall remedy/structural necessity remains unknown rather than declaring semantics invalid.
- Review corrections: Correct research structural_change=no to unknown for the unresolved warning feature; the demonstrated local emitter escape covers only one instance. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## string_template_multi_placeholder_slot_not_found_2026-07-30 — Two bare `_` placeholders in one string template: `variable __p1 not found`

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/string_template_multi_placeholder_slot_not_found_2026-07-30.md#L1-L292; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/expressions/placeholder.rs#L291-L345; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/placeholder_lambda.spl#L613-L635; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/desugar/placeholder_lambda.spl#L748-L805; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl#L804-L882; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/frontend/placeholder_lambda_fstring_shared_slot_spec.spl
```
- Review rationale: Full report supersedes its early unknown mechanism with the Rust FString occurrence-count bug. Independently read current presence-count branch, single-slot replacement and exact two-region regression asserting __p0 for both tuple fields. Thus the seed repair is concrete. The report separately identifies an unwired pure-Simple mirror; current FlatAstBridge constructs individual interpolation expressions. Retain unknown overall family remedy because seed unit-source evidence does not establish self-hosted template-lambda routing; do not repeat the superseded claim that the original Rust root was unknown.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## struct_dict_field_mutation_engine_divergence_2026-08-10 — Dict-in-struct field mutation through a by-value receiver diverges by engine, silently losing writes

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/struct_dict_field_mutation_engine_divergence_2026-08-10.md#L1-L160; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs#L1179-L1225; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs#L1544-L1574; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/service/lease_manager.spl#L77-L205; test/01_unit/compiler/interpreter/self_field_assign_spec.spl (report’s recorded red test)
```
- Review rationale: The full report's argument-boundary control passed while return-boundary Dict mutation failed; it leaves embedded-container copy depth undecided. Current function_exec recursively merges changed Array/Dict/ByteArray fields and invokes that helper on returned value-type struct arguments. LeaseManager is now a class with mutating methods, avoiding its local state-loss shape. These are substantive current changes, but neither settles the language contract nor proves all engines agree. Unknown overall solution/structure retained.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## struct_param_mutation_semantics_2026-07-03 — Struct/class param mutation semantics — decision doc (task #35)

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/struct_param_mutation_semantics_2026-07-03.md#L1-L160; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs#L1179-L1225; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs#L1544-L1574; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/service/lease_manager.spl#L77-L205; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/07_guide/language/value_semantics_by_engine.md (report cited)
```
- Review rationale: Complete decision report reverses the initial blame: interpreter preserves the class mutation, while compiled cross-module behavior loses it; struct non-mut capability enforcement is a separate issue. Current function_exec has capability-dependent writeback and special collection-field merging for value-type structs. This does not establish current class/struct, plain/mut, fn/me parity across engines. No unilateral copy-depth or class-reference decision is made; keep the historical divergence valid with unknown remedy.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## struct_spread_paren_form_parses_as_range_2026-08-30 — Paren-form struct spread `T(..base, f: v)` parses as a RANGE, and hangs the compiler (2026-08-30)

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/struct_spread_paren_form_parses_as_range_2026-08-30.md#L1-L118; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/parser/src/expressions/helpers.rs#L470-L525; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl#L1418-L1434; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl#L647-L662; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl#L6212-L6363; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_native.c#L10387-L10418; test/01_unit/compiler/50.mir/array_move_lowering_spec.spl#L516-L520
```
- Review rationale: The report's old paren-spread range carrier led to rt_range materialization. Current parser detects leading constructor spread; FlatAstBridge preserves EXPR_SPREAD as the established no-start Range carrier; lower_struct_construct extracts it before positional arguments, evaluates the base once, and copies unclaimed fields. This is a causally specific implementation repair for the constructor route, beyond the old with_blocks workaround. Broader brace/module-level and runtime parity are not qualified; exact paren-form execution remains untested.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fixed_pending_verification.

## sub_sup_line_box_strut_contradiction_2026-09-14 — `<sub>`/`<sup>` line box is the inline's own height, and the obvious strut fix contradicts Chrome (2026-09-14)

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/sub_sup_line_box_strut_contradiction_2026-09-14.md#L1-L79; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl#L1781-L1802; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_foundation.spl#L274-L291; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout_engine.spl#L1916
```
- Review rationale: Read all geometry measurements and rejected patch rationale. Current split renderer still seeds inline_line_h from cst; foundation align_inline_line_baselines returns supplied height unchanged for an empty node list before strut ascent/descent initialization. This preserves the reported sub/sup-only gap. Report's numeric versus absolute line-height contradiction and single-size sup evidence prevent a supported general repair; no formula is inferred from one sample.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## supervised_builder_unwired_and_no_peak_rss_2026-08-17 — Supervised builder: not yet wired to a front end, and peak RSS is always 0

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/supervised_builder_unwired_and_no_peak_rss_2026-08-17.md#L1-L143; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/parallel.spl#L816-L875; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_aot_native_output.spl#L847; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/build_outcome.spl#L228-L265
```
- Review rationale: Full report includes four distinct gaps and explicitly explains that frozen in-process capsules cannot be cheaply handed to a child; a full compiler reload per module is unacceptable. Current build_supervised requires spawn_fn(path), tracks children and constructs outcomes, while scoped driver/CLI search finds only its declaration/comments and no frontend call. This confirms integration gap, not one trivial branch fix. Child peak RSS, incremental resume and six-module acceptance remain separately unqualified; no single established remedy.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## svmg_lowering_spec_unterminated_fstring_parse_failure_2026-09-13 — `test/01_unit/compiler/backend/svmg_lowering_spec.spl` fails to parse: "Unterminated f-string"

- Source receipt: `adjudication_v2_27`; inspection `report_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/svmg_lowering_spec_unterminated_fstring_parse_failure_2026-09-13.md#L1-L78; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/backend/svmg_lowering_spec.spl#L332-L350; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer_struct.spl#L818-L871; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/lexer_struct.spl#L1137-L1165
```
- Review rationale: Complete report records deployed aarch64 seed rejecting the whole SVMG spec as unterminated f-string while x={0} succeeds alone; no error position or complete reduction exists. Current cited fixture remains the intended string-interpolation rejection test. The inspected pure-Simple lexer is not bound to that historical seed error, so no active causal owner or invalidity is established. Accepted uncertain/unknown, with next step a qualified syntax-complete reduction.
- Review corrections: Downgrade source_reviewed to report_reviewed: the inspected generic lexer termination branches are not demonstrated to produce this seed-specific failure. Versus frozen queue: validity: valid -> uncertain.

## system_cover_gate_reports_791_legacy_feature_specs_as_failures_2026-08-04 — @cover gate marks 791 un-annotated test/03_system/feature specs as FAILURES not skips

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/system_cover_gate_reports_791_legacy_feature_specs_as_failures_2026-08-04.md#L1-L120; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_main.spl#L347-L369; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/cover_admission.spl
```
- Review rationale: Full report preserves intentional cover policy and requires truthful per-spec migration. Current normal runner returns cover_append_failures before admitted specs execute; unstable mode filters rejected files and continues. The append helper inserts failed:1 and increments total_failed despite saying test not executed. Distinguishing policy-admission outcomes from assertion failures and consistently executing admitted files is a causal remedy, but it changes the result contract consumed by CI and requires coordinated consumer review; annotations cannot be fabricated.
- Review corrections: Correct research structural_change=no to yes: the report and current TestRunResult aggregation show a cross-consumer result-contract change, not merely local formatting. Keep_open; no policy bypass. Versus frozen queue: solution: unknown -> known; structural_change: unknown -> yes; inspection_level: report_reviewed -> source_reviewed.

## t32_directory_alias_snapshot_provider_missing_2026_10_12 — Directory alias provider omitted from admitted compiler snapshot

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_entrypoint/inventory_aliases.spl:1-147; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_entrypoint/inventory_events.spl:736-756; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/02_integration/app/compiler_inventory_directory_alias_spec.spl:1-98; frozen input/open_bugs_08.tsv exact bug row/description
```
- Review rationale: Read frozen issue description and full current alias owner. Resolver maps tracked directory aliases to logical child identities, refuses checkout escapes/build-private owners/nested links, verifies readback identities, and inventory_events merges aliases into authenticated membership before admission. The real-Git lifecycle spec is explicitly authored UNRUN. This is a concrete cross-owner source-inventory repair; optional-array ANY.link failure is a separate compiler qualification blocker, not proof alias semantics failed or passed.
- Review corrections: Change research keep_open to fixed_pending_verification for the source-provider repair, while preserving untested and separate build/latency/RSS/nested-alias qualification gaps. No authority recreation or policy weakening. Versus frozen queue: solution: unknown -> known; structural_change: unknown -> yes; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fixed_pending_verification.

## target_instruction_optimization_32bit_spec_pre_existing_red_2026-08-27 — target_instruction_optimization_32bit_spec pre-existing RED — std.spec does not export 'SPipe'

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/target_instruction_optimization_32bit_spec_pre_existing_red_2026-08-27.md:1-31; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/app/compiler/feature/target_instruction_optimization_32bit_spec.spl:1-48; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec.spl:497-500; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/spec/__init__.spl:49-56
```
- Review rationale: Complete report records missing std.spec.SPipe before 29 examples and proves the then-comment-only edit was unrelated. At c0 moved spec now imports std.spec.step and std.spec. Independently read canonical spec.spl public step and package __init__ step/export; earlier inspected resolver selects project stdlib. Removing the obsolete SPipe import addresses this exact load blocker in source. Historical bug remains valid; executing current spec or claiming all 29 behaviors pass is outside this review.
- Review corrections: Correct research uncertain/unknown/keep_open to valid/known/fixed_pending_verification for the exact obsolete import blocker, after checking the replacement step exports. The fixture's own local helper semantics are not certified. Versus frozen queue: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fixed_pending_verification.

## task_spawn_runtime_pool_spec_semantic_fail_2026-07-05 — task_spawn_runtime_pool_spec.spl: semantic error — cannot assign field on non-object value

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/task_spawn_runtime_pool_spec_semantic_fail_2026-07-05.md#L1-L39; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl#L1-L24; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/thread_pool.spl#L16-L36; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/thread_pool.spl#L268-L316; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/thread_pool.spl#L441-L477
```
- Review rationale: Full report records cannot-assign-field-on-non-object and explicitly excludes this fixture from substituted identity-spec evidence. Current fixture only task_spawns four closures and sums joined results; task_spawn constructs TaskHandle after registering a multicore handle, and TaskHandle.join writes cached_result/joined. This is a relevant producer/writeback trace, but does not identify which historical assignment received a non-object. Keep valid/unknown; separate passing identity coverage is not a repair.
- Review corrections: Independent adjudication supports the stated categories; historical executions remain untested here. Evidence SHA typos normalized where present. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## tautology_guarded_skip_specs_false_green_family_2026-08-04 — Tautology-guarded skip specs report green without executing; repo-wide family, census inco

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tautology_guarded_skip_specs_false_green_family_2026-08-04.md:1-178,1278-1599; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/desugar/forwarding_spec.spl:1-192 (only lines1-4 executable); c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/app/desugar/context_params_spec.spl:1-15; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/bdd.rs:1148-1173
```
- Review rationale: Read canonical mechanism, correction/repair sections and pending-verdict caveat, without adopting historical census counts as current. Independently inspected every executable line of c0 forwarding_spec: only a literal pending_reason and len()>0 assertion execute; its intended forwarding tests are all comments. By contrast context_params_spec has the same tautology plus real tests, so a regex match alone does not show all coverage suppressed. Current Rust pending fallback still increments BDD_COUNTS.0 when no Simple owner exists. Family is demonstrably valid, but blanket replace-with-pending is not a proven family remedy and no uniform structural change is established.
- Review corrections: Reject research known/yes: generic real-assertion/pending advice does not resolve heterogeneous gutted, uncoupled and environment-gated cases; pending itself has result-accounting caveats. Add actual live guarded-spec evidence rather than rely on trait_scanner or a candidate count. Versus frozen queue: inspection_level: report_reviewed -> source_reviewed.

## tcp_peer_probe_feature_missing_2026-09-16 — Non-consuming TCP peer probe (TcpPeerProbe / rt_io_tcp_probe_peer) missing

- Source receipt: `adjudication_v2_27`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tcp_peer_probe_feature_missing_2026-09-16.md#L1-L30; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/nogc_async_mut/http_server/async_ssr_peer_probe_contract_spec.spl#L1-L30; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/io/driver.spl#L50-L66; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/net/tcp_shim.spl
```
- Review rationale: Read full missing-feature report and exact contract spec. Current driver declares consuming TCP read/write/close APIs; scoped exact-target search finds neither TcpPeerProbe nor rt_io_tcp_probe_peer in driver/IO subtree or SimpleOS shim. Contract asserts four states and Unsupported=3 without net_tcp_read, so absence is a legitimate feature gap. It necessarily adds a driver/OS contract, but no supported implementation for non-consuming hosted probing is demonstrated. Implement-the-feature is not a known root solution.
- Review corrections: Downgrade research solution=known to unknown. Retain structural_change=yes because required enum/API and backend shim extend an explicit cross-module contract; no consuming-read workaround or spec retirement is accepted. Versus frozen queue: structural_change: unknown -> yes; inspection_level: report_reviewed -> source_reviewed.

## test_coverage_wrapper_native_build_refused_by_scv_admission_2026_10_19 — --coverage aborts every spec: wrapper native-build refused by SCV admission

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/bug_db.sdn (matching coverage description); c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:878-887,1024-1034; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/native_loader/src/process_provider.rs:34-49
```
- Review rationale: Cold-init only on absent journals and Large budget are present; exact-first libc lookup is present. The detailed DB report still records HIR object-to-i64 failure after admission repairs. Diagnostic picking cannot establish end-to-end coverage. No single remaining remedy is established.
- Review corrections: inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## test_daemon_freezes_env_binary_override_dead_2026-08-02 — Long-lived light daemon freezes env, so SIMPLE_* binary override is silently ignored

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_daemon_freezes_env_binary_override_dead_2026-08-02.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_daemon/environment_identity.spl:12-58; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_daemon/light_protocol.spl:47-72; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_daemon/light_daemon.spl:176-189; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_client.spl:379-391,491-528,534-546,831-900; historical bb3f6ab8ab2 inspected via git log bound to c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: Historical stale-daemon environment report is supported. Independently traced normalized environment hashing, v2 digest/generation encoding, daemon rejection and client reroute to direct execution (client 379-391,867-900). This source remedy avoids reusing a mismatched environment; deployment and regression execution remain unqualified.
- Review corrections: solution: unknown -> known; structural_change: unknown -> yes; recommended_action: keep_open -> fixed_pending_verification. Independent review supersedes low proposal where stale: Historical stale-daemon environment report is supported. Independently traced normalized environment hashing, v2 digest/generation encoding, daemon rejection and client reroute to direct execution (client 379-391,867-900). This source remedy avoids reusing a mismatched environment; deployment and regression execution remain unqualified. See independent rationale.

## test_mode_filter_specs_are_vacuous_self_tests_2026-08-21 — Test mode-filter specs are vacuous self-tests, and the skip marker they assert on is corrupted

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_mode_filter_specs_are_vacuous_self_tests_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/mode_filter.spl:20-112; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/test_runner/mode_filter_spec.spl:25-100; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/feature/mode_filter/skip_native_spec.spl:11-22; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_main.spl:847-856
```
- Review rationale: Contrary to low research, the unit spec now imports std.test_runner.mode_filter and production dispatch calls path_mode_matches at main:854. The module parses @skip_mode, while skip_native_spec still uses skip-marker-removed_mode and expect(true). Correct that fixture to the supported directive and an actual mode observation; primary unit self-reimplementation has already been repaired.
- Review corrections: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fix_candidate. Independent review supersedes low proposal where stale: Contrary to low research, the unit spec now imports std.test_runner.mode_filter and production dispatch calls path_mode_matches at main:854. The module parses @skip_mode, while skip_native_spec still uses skip-marker-removed_mode and expect(true). Correct that fixture to the supported directive and an actual mode observation; primary unit self-reimplementation has already been repaired. See independent rationale.

## test_runner_env_passthrough_2026-07-29 — Custom env vars set before bin/simple test are stale inside it bodies (daemon-frozen env)

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_env_passthrough_2026-07-29.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_daemon/environment_identity.spl:12-58; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_daemon/light_protocol.spl:47-72; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_daemon/light_daemon.spl:176-189; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_client.spl:379-391,491-528,534-546,831-900; historical bb3f6ab8ab2 inspected via git log bound to c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: The historical report documents stale inherited daemon env. Current v2 request carries environment digest and generation, client checks both before submitting and consumes reroute to run_one_direct; daemon refuses mismatch before spawn. This is a concrete protocol/reuse remedy for the reported route. No current executable was qualified.
- Review corrections: solution: unknown -> known; structural_change: unknown -> yes; recommended_action: keep_open -> fixed_pending_verification. Independent review supersedes low proposal where stale: The historical report documents stale inherited daemon env. Current v2 request carries environment digest and generation, client checks both before submitting and consumes reroute to run_one_direct; daemon refuses mismatch before spawn. This is a concrete protocol/reuse remedy for the reported route. No current executable was qualified. See independent rationale.

## test_runner_exits_zero_on_failed_spec_2026-08-21 — `bin/simple test` exits 0 while its own verdict reports failed=1

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_exits_zero_on_failed_spec_2026-08-21.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/driver/src/cli/basic.rs:255-347; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_types.spl:321-348,433-443; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_main.spl:1460-1564; historical 4b88aebf00b inspected via git log bound to c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: Seed verdict owner now tallies failed before downgrading Ok and zero status. Pure-Simple aggregate maps total_failed to AssertionOrChildFailure, maps that to exit 1, and main propagates spec_exit_code to its final return. These bounded tally/return repairs address the reported false green; current execution remains untested.
- Review corrections: solution: unknown -> known; structural_change: unknown -> no; recommended_action: keep_open -> fixed_pending_verification. Source-level assessment changes solution from unknown to known and action from keep_open to fixed_pending_verification; both reported source remedies are present, with runtime verification pending. See independent rationale.

## test_runner_in_development_reporting_and_db_persist_2026-08-23 — In-development reporting mislabels neutralised specs, breaks total conservation, and never persists to the test DB

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_in_development_reporting_and_db_persist_2026-08-23.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_daemon/light_protocol.spl:232-263; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_main.spl:102-149,1460-1484
```
- Review rationale: Report has four distinct render/conservation/persistence defects plus an opt-in Rust twin. ran_verdict_line now counts in_development as executed. Main uses record_test_run_via_db_lane before summary, with bounded child and warnings on write/child errors. These repairs do not establish total conservation, per-file labelling or successful database rows across all lanes; no complete remedy established.

## test_runner_never_exits_after_summary_post_run_db_report_2026-08-18 — `simple test <dir>` prints its complete summary and then never exits (post-run DB/report phase)

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_never_exits_after_summary_post_run_db_report_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_main.spl:102-149,1460-1564
```
- Review rationale: Historical ablation connects seed nonexit to DB/report work but expressly leaves residual teardown unexplained. Current persistence is moved into a bounded 600000ms child before summary; coverage/doctest and result encoding precede final exit_code. Source evolution does not diagnose the seed residual or prove runtime termination; --no-db is only a workaround.

## test_runner_peak_rss_needs_child_rusage_extern_2026-08-17 — Supervised test runner cannot report peak RSS — no child-rusage extern exists

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_peak_rss_needs_child_rusage_extern_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_process_owned.c:352-359,4234-4279; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_extern/system.rs:1138-1172; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/resource_scope.spl:725-768; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/native_owned_process.spl:24-57; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl:257-265,323-335; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_runner_output.spl:203-211; historical 88aac2ffe28 inspected via git log bound to c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: Per-child wait4 rusage is captured in runtime_process_owned.c:4234-4279, converted to bytes with Apple-specific units, exposed by interpreter_extern/system.rs:1138-1168 and scoped child usage, then serialized by test_runner_output:203-211. This supersedes the no-field/no-capture premise. Optional provider evidence and current binary behavior still require qualification.
- Review corrections: solution: unknown -> known; structural_change: unknown -> yes; recommended_action: keep_open -> fixed_pending_verification. Source-level assessment changes solution to known and action to fixed_pending_verification; the requested measurement contract is now present across runtime, binding, runner result, and output/DB paths. See independent rationale.

## test_runner_reports_only_last_failure_per_example_2026-08-04 — Runner reports only the LAST failure per example, hiding earlier assertion failures

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_reports_only_last_failure_per_example_2026-08-04.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_call/bdd.rs:36-45,1053; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/interpreter_method/mod.rs:580-596
```
- Review rationale: Historical probe isolates the last failure, not last assertion. Both record_assertion_failure and the actual chained to_equal mismatch arm overwrite one BDD_FAILURE_MSG Option<String>; a later passing matcher preserves the failure flag. This confirms the reported lost diagnostic mechanism. Whether the intended reporting contract should aggregate every assertion remains unresolved; isolation into separate examples is a workaround, not an admitted fix.
- Review corrections: inspection_level: report_reviewed -> source_reviewed. Low known remedy downgraded: standalone assertion storage alone does not establish all matcher/render paths or their contract. See independent rationale.

## test_runner_spins_at_100pct_after_summary_2026-08-18 — `bin/simple test` keeps one thread at 100% CPU after printing its final summary

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_spins_at_100pct_after_summary_2026-08-18.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_main.spl:102-149,1460-1564
```
- Review rationale: Report distinguishes CPU-monitor repair from unexplained interpreter spin and later retracts the dead test_db_core diagnosis. Live test_extended optimization was explicitly held unlanded after killed A/B runs. Current main runs bounded DB child before summary and returns exit_code after coverage/doctests; this does not prove teardown termination. Retain unknown root remedy.

## test_runner_windows_child_binary_stale_fallback_2026-09-01 — `simple test` on Windows silently runs specs on a STALE `bin/simple`, not the invoking binary

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_runner_windows_child_binary_stale_fallback_2026-09-01.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/test_runner_new/test_runner_single.spl:390-422; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl:143-167,194-275
```
- Review rationale: Current app single runner uses cross-platform current executable identity and rejects mismatched SIMPLE_BINARY. Library executor probes own PID through PowerShell on Windows but still has deployed candidate fallbacks after failed authority discovery. Original stale child evidence remains valid; Windows discovery failure and route reachability need qualified execution before a complete remedy can be claimed.

## test_tree_divergence_preexisting_2026-08-17 — Pre-existing test-tree divergence, and the mirror the ed25519 fix missed

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_tree_divergence_preexisting_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-test-tree-divergence.shs:640-690; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/test/test_tree_divergence_preexisting_2026-08-17.txt; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/verification/lean_workflow_spec.spl:22-25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/unit/compiler/verification/lean_workflow_spec.spl:22-25; historical 1dabf89356d inspected via git log bound to c0b3ad911f4cb00c0f3550b05baa8d06347d17d0
```
- Review rationale: The report separates its repaired ed25519 mirror from the broad historical backlog. Exact c0 ancestry records later removal of that legacy twin (1dabf89356d). Current guard still distinguishes new divergences from fixed baseline entries. The historical offender artifact includes lean_workflow, whose surviving current twins assert different proof-state methods. That supports unresolved reconciliation work but not the old numeric census or a single remedy.
- Review corrections: validity: valid -> uncertain; inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## test_tree_divergence_preexisting_red_2026-08-16 — Pre-existing test-tree divergence red at `f6cadcc36af` — step-over record

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_tree_divergence_preexisting_red_2026-08-16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-test-tree-divergence.shs:640-690; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/verification/lean_workflow_spec.spl:22-25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/unit/compiler/verification/lean_workflow_spec.spl:22-25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/os/kernel/arch/riscv64_syscall_ipc_spec.spl:42-47; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/unit/os/kernel/arch/riscv64_syscall_ipc_spec.spl:42-47
```
- Review rationale: Independently compared all 16 specifically named paths at c0: seven pairs remain byte-divergent, eight original divergent legacy twins are absent, and the stale async_host legacy twin is absent. The lean_workflow pair uses is_model_complete versus is_fully_proven, and riscv64 syscall setup differs substantively. Current 15-new count is stale; differences need owner review rather than blanket baselining.
- Review corrections: inspection_level: report_reviewed -> source_reviewed. Independent comparison corrects low research count: seven current divergent pairs, not eight; nine legacy twins absent including stale async_host. See independent rationale.

## test_tree_divergence_preexisting_red_stepover_2026-08-17 — Pre-existing test-tree divergence red — recorded step-over (2026-08-17)

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_tree_divergence_preexisting_red_stepover_2026-08-17.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-test-tree-divergence.shs:640-690; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/test/test_tree_divergence_preexisting_2026-08-17.txt; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/verification/lean_workflow_spec.spl:22-25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/unit/compiler/verification/lean_workflow_spec.spl:22-25
```
- Review rationale: Read complete step-over narrative and current guard baseline-difference semantics. Historical 876-entry artifact includes lean_workflow; its current twins differ in proof-state assertions. Thus the historical delta PASS does not demonstrate reconciliation, but the 64-new/5-mirror-only counts cannot be asserted at c0 without a complete artifact-to-current comparison. Conservative unresolved backlog classification accepted, not a completed census.
- Review corrections: validity: valid -> uncertain; inspection_level: report_reviewed -> source_reviewed.  See independent rationale.

## test_tree_divergence_preexisting_step_over_2026-08-16 — Pre-existing test-tree divergence stepped over on 2026-08-16

- Source receipt: `adjudication_v2_28`; inspection `source_reviewed`; state `accepted`.
- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Evidence refs (verbatim source field; no inferred links; external refs are not archived by this checkpoint):
```text
c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/test_tree_divergence_preexisting_step_over_2026-08-16.md; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-test-tree-divergence.shs:640-690; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/verification/lean_workflow_spec.spl:22-25; c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/unit/compiler/verification/lean_workflow_spec.spl:22-25
```
- Review rationale: Report has contradictory Closed bookkeeping and explicit open/unfixed narrative, plus a later browser-lane step-over. Both historical lists include lean_workflow whose current twins still assert different proof predicates. Guard baseline generation merely copies observed differences, so neither status stamp nor delta PASS establishes repair. Exact remaining backlog and per-pair remedy remain unknown.
- Review corrections: validity: valid -> uncertain; inspection_level: report_reviewed -> source_reviewed.  See independent rationale.
