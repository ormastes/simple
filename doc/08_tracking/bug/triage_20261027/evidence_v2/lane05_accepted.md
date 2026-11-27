# V2 lane 05 accepted review evidence

Accepted classifications captured: 35. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

## native_huffman_untyped_return_guard_2026_10_11 — Native Huffman untyped returns block normal object generation

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_huffman_untyped_return_guard_2026_10_11`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_huffman_untyped_return_guard_2026_10_11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_huffman_untyped_return_guard_2026_10_11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/compression/gzip/huffman.spl:17](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/compression/gzip/huffman.spl#L17)
- Review rationale: The report documents an unannotated-return HIR rejection and later annotated Huffman object/fixture qualification. Current fixed-table helpers declare nested-array return types and huffman_lookup returns [i64]?. These consumer contracts do not establish a repaired compiler inference rule; keep the original defect open and current execution untested.
- Review corrections: validity: uncertain -> valid; inspection_level: metadata_only -> source_reviewed

## native_identity_i64_receiver_type_loss_2026_10_11 — Known i64 identity receivers lose MIR method provenance

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_identity_i64_receiver_type_loss_2026_10_11`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_identity_i64_receiver_type_loss_2026-10-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_identity_i64_receiver_type_loss_2026-10-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/native_capsule_mir_identity.spl:95](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/native_capsule_mir_identity.spl#L95)
- Review rationale: C35 report records unresolved integer to_text placeholders and a construction timeout, explicitly without exact warning-to-site mapping. Current serializer retains four typed i64 aliases before to_text. This is a provenance-preserving workaround, not proof of the MIR root repair or current failure.
- Review corrections: validity: uncertain -> valid; inspection_level: metadata_only -> source_reviewed

## native_negative_literal_match_patterns_2026_10_10 — Negative integer patterns become multiple wildcard arms

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_negative_literal_match_patterns_2026_10_10`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_negative_literal_match_patterns_2026_10_10.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_negative_literal_match_patterns_2026_10_10.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/cli/native_build_exit_status.spl:2](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/cli/native_build_exit_status.spl#L2)
- Review rationale: The original signed-literal match produced multiple wildcard arms; current helper replaces it with seven ordered equality branches and keeps POSIX signal bounds distinct. The report qualifies that workaround with a historical fixture, explicitly not negative-pattern lowering. No current runtime result or root fix inferred.
- Review corrections: validity: uncertain -> valid; inspection_level: metadata_only -> source_reviewed

## native_optional_array_pattern_binder_i64_2026_10_21 — preserve_declared_sdn_array_element_type_until_pattern_binder_lowering_is_rebuilt

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_optional_array_pattern_binder_i64_2026_10_21`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_optional_array_pattern_binder_i64_2026_10_21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_optional_array_pattern_binder_i64_2026_10_21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/incremental.spl:1154](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_build/incremental.spl#L1154)
- Review rationale: Report pinpoints issue143 on iteration of SdnValue.as_array optional payload. Current BuildCache.load binds entries_array_raw then explicitly declares [SdnValue] before iteration, preserving missing values. It confirms the compatibility workaround, not a repaired optional pattern binder; diagnosis scope stays unknown.
- Review corrections: validity: uncertain -> valid

## native_optional_fn_payload_binding_arity_mir_2026_10_20 — declared_fn_parameter_gives_the_indirect_call_its_proven_signature

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_optional_fn_payload_binding_arity_mir_2026_10_20`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_optional_fn_payload_binding_arity_mir_2026_10_20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_optional_fn_payload_binding_arity_mir_2026_10_20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser.spl:1090](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser.spl#L1090); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/parallel.spl:379](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_build/parallel.spl#L379); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser.spl:1101](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser.spl#L1101)
- Review rationale: Full report corrects initial MIR theory: explicit Option<T> erased callable inners below TYPE_NAMED_BASE. Current parser registers is_function_tag inners in the generic Option registry; both ParallelBuilder calls still use typed helper. This supports a historical valid defect and partial parser repair, but the complete indirect-call payload path remains unqualified; root solution/structural scope remain unknown.
- Review corrections: validity: uncertain -> valid

## native_optional_payload_owner_dispatch_2026_10_26 — native optional payload owner dispatch (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_optional_payload_owner_dispatch_2026_10_26`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_optional_payload_owner_dispatch_2026-10-26.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_optional_payload_owner_dispatch_2026-10-26.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl:354](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl#L354)
- Review rationale: Original mixed optional/payload match failed even after qualifying Tuple/Struct because Option and payload owners collided. Current hs_enum_payload and hs_pattern_payload unwrap first and exhaustively match distinct nominal owners, retaining fail-loud nil output checks. Historical actual-owner controls qualify only this marked workaround; compiler owner resolution remains open.

## native_optional_struct_pointer_nil_2026_10_11 — Optional struct binding emits invalid pointer nil constant

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_optional_struct_pointer_nil_2026_10_11`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_optional_struct_pointer_nil_2026_10_11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_optional_struct_pointer_nil_2026_10_11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/40.mono/monomorphize/tracker.spl:137](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/40.mono/monomorphize/tracker.spl#L137)
- Review rationale: Report records LLVM add ptr3 for absent BuildMetadata if-val. Current tracker uses explicit Some and nil match arms when copying build metadata. This avoids ExistsCheck but does not prove repaired nil materialization; ARM object success in an old receipt is not present/absent runtime qualification.
- Review corrections: validity: uncertain -> valid; inspection_level: metadata_only -> source_reviewed

## native_raw_integer_optional_presence_2026_10_26 — native to_i64 returns raw i64 under ?? presence test

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_raw_integer_optional_presence_2026_10_26`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_inventory_decimal_optional_2026_10_26.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_inventory_decimal_optional_2026_10_26.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/scv/compile_source_inventory.spl:420](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/scv/compile_source_inventory.spl#L420)
- Review rationale: Retained disassembly shows rt_string_to_int_lenient returning raw 3 while coalesce tests it as Option. Current decimal parser returns explicit validity/value and checks canonical spelling and overflow before multiply/add. It repairs this consumer without changing the compiler/provider ABI; root solution remains unknown.
- Review corrections: validity: uncertain -> valid

## native_result_try_payload_text_type_lost_2026_10_10 — Result try payload loses text provenance

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_result_try_payload_text_type_lost_2026_10_10`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_result_try_payload_text_type_lost_2026_10_10.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_result_try_payload_text_type_lost_2026_10_10.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:5644](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl#L5644); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl:480](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl#L480)
- Review rationale: Full report isolates Result? declared-text type loss. Current lower_try decodes Result ok_type through decode_declared_enum_payload_slot, which lowers expected type and records HIR type; fallback recovers lowered-call declaration. This supports repaired type transport but does not fully qualify text carrier/runtime ABI, so retain unknown root-completion and keep open.
- Review corrections: validity: uncertain -> valid; inspection_level: report_reviewed -> source_reviewed

## native_sdn_empty_payload_owner_2026_10_11 — Empty SDN enum containers lose payload type

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_sdn_empty_payload_owner_2026_10_11`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_sdn_empty_payload_owner_2026_10_11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_sdn_empty_payload_owner_2026_10_11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/sdn/value.spl:56](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/sdn/value.spl#L56)
- Review rationale: C35 rejected untyped empty Array/Dict payloads; current SdnValue constructors give empty locals explicit [SdnValue] and Dict<text,SdnValue> types. ARM fixture and later parser-object evidence are historical and limited; neither repairs enum constructor inference.
- Review corrections: validity: uncertain -> valid; inspection_level: metadata_only -> source_reviewed

## native_text_scalar_validation_failure_2026_10_18 — use-existing-pure-utf8-owners-for-scalar-validation

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_text_scalar_validation_failure_2026_10_18`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_text_scalar_validation_failure_2026_10_18.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_text_scalar_validation_failure_2026_10_18.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/fixtures/repro/compiler/char_wire_scalar_cast/main.spl:8](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/fixtures/repro/compiler/char_wire_scalar_cast/main.spl#L8)
- Review rationale: Original public helper conjunction rejects ASCII at exit13, without isolating either helper. Current probe instead decodes and re-encodes every UTF-8 byte, distinguishing malformed input from valid U+FFFD. Historical workaround PASS does not repair public SIMD validation or qualify CharLit codec.

## native_u8_array_ne_compares_reference_2026_10_25 — native [u8] != compares references; element-wise compare

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#native_u8_array_ne_compares_reference_2026_10_25`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/native_u8_array_ne_compares_reference_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/native_u8_array_ne_compares_reference_2026-10-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/retained_file.spl:291](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io/retained_file.spl#L291)
- Review rationale: Current retained-file identity compares byte-array length then each element, replacing native reference comparison. Full report supplies equal-content two-handle discrimination and historical successful workaround. This addresses the caller, not array equality lowering.
- Review corrections: validity: uncertain -> valid

## nll_live_aliases_method_arg_corruption_2026_10_22 — self_receiver_plus_array_arg_method_call_miscompiles_in_native_candidate

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#nll_live_aliases_method_arg_corruption_2026_10_22`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/55.borrow/borrow_check/nll.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/55.borrow/borrow_check/nll.spl); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/55.borrow/borrow_check/nll.spl:342](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/55.borrow/borrow_check/nll.spl#L342)
- Review rationale: Current nll_live_aliases free helper filters LoanAlias entries by local liveness; adjacent diagnostic records empty array becoming garbage across self-plus-array method call. This is a call-shape workaround, not NLL algorithm repair; compiler owner remains unisolated.
- Review corrections: inspection_level: report_reviewed -> source_reviewed

## notebook_cuda_exec_jit_lane_not_implemented_2026-08-08 — CudaExec cannot back jit(remote(cuda(...))) cells: no per-cell PTX compile path exists

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#notebook_cuda_exec_jit_lane_not_implemented_2026-08-08`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/notebook/cuda_exec.spl:132](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/notebook/cuda_exec.spl#L132)
- Review rationale: CudaExec explicitly blocks JIT notebook probe/start/execute paths while interpreter initializes fixed PTX. Full report requires arbitrary per-cell source compilation, so the guard is honest but capability remains absent. Root implementation/architecture choice is unresolved.
- Review corrections: validity: uncertain -> valid; inspection_level: metadata_only -> source_reviewed

## office_plan_acceptance_spec_reads_wrong_evidence_root_2026-09-06 — Office plan-acceptance spec reads an evidence root the gate never writes

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#office_plan_acceptance_spec_reads_wrong_evidence_root_2026-09-06`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/office_plan_acceptance_spec_reads_wrong_evidence_root_2026-09-06.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/office_plan_acceptance_spec_reads_wrong_evidence_root_2026-09-06.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/03_system/plan_acceptance/office_cli_tui_ui_access_spec.spl:24](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/03_system/plan_acceptance/office_cli_tui_ui_access_spec.spl#L24); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-office-cli-tui-ui-access.spl:73](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-office-cli-tui-ui-access.spl#L73)
- Review rationale: The spec constructs plan_acceptance/.../runs/ plus handoff run ID, while invoked gate constructs app/office/feature/.../runs/ for the same ID. Current source confirms mismatch and unique-run gate guard. Align the spec locator with gate base while preserving unique run IDs; this is local path plumbing.
- Review corrections: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fix_candidate

## one_element_literal_of_loop_text_boxed_as_int_2026-10-25 — one element literal of loop text boxed as int (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#one_element_literal_of_loop_text_boxed_as_int_2026-10-25`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/one_element_literal_of_loop_text_boxed_as_int_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/one_element_literal_of_loop_text_boxed_as_int_2026-10-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/cache/native_interface_slice.spl:246](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/cache/native_interface_slice.spl#L246)
- Review rationale: Current trailing-attribute loop explicitly rebinds attr as text before one-element array construction. Full report shows plain loop-text literal control passed, while actual alias/accumulation shape crashed and typed twin passed. Workaround is shape-specific; original MIR provenance root remains open.

## optional_array_payload_narrowing_native_2026_10_21 — old_producer_does_not_narrow_optional_array_after_nil_guard

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#optional_array_payload_narrowing_native_2026_10_21`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_schema/fold_gen.spl](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/compiler_schema/fold_gen.spl); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_schema/fold_gen.spl:317](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/compiler_schema/fold_gen.spl#L317)
- Review rationale: Generator emits explicit typed non-null local for optional array in the non-nil branch, then recursively hashes the underlying array type. This is a compiler narrowing workaround; original producer evidence and root repair are absent, so keep validity uncertain without inventing a fix.
- Review corrections: inspection_level: metadata_only -> source_reviewed

## optional_field_read_after_nil_check_reads_option_box_2026-10-25 — optional field read after nil check reads option box (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#optional_field_read_after_nil_check_reads_option_box_2026-10-25`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/optional_field_read_after_nil_check_reads_option_box_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/optional_field_read_after_nil_check_reads_option_box_2026-10-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:662](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl#L662)
- Review rationale: Report ties integer accumulation loss to optional MirType field read observing the Some box, causing array merge fallback. Current scalar predicate explicitly binds the payload and rejects absence before discriminant checks. This repairs consumer dispatch only; compiler narrowing/field unboxing remains open.

## optional_text_unwrap_truncates_at_nul_2026-10-25 — optional text unwrap truncates at nul (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#optional_text_unwrap_truncates_at_nul_2026-10-25`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/optional_text_unwrap_truncates_at_nul_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/optional_text_unwrap_truncates_at_nul_2026-10-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/compiler_entrypoint/inventory_scratch.spl:30](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/compiler_entrypoint/inventory_scratch.spl#L30)
- Review rationale: Native text? unwrap loses byte length at rt_interp_cstr; report contrasts 4158-byte prefix with 11465-byte file and full coalesce control. Current inventory path uses content coalesce after absence rejection. This avoids truncation locally; native optional-text decoder root remains open.

## optional_try_nominal_owner_missing_2026_10_21 — Keep the declared table owner until rebuilt Try metadata recovery is qualified

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#optional_try_nominal_owner_missing_2026_10_21`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/optional_try_nominal_owner_missing_2026_10_21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/optional_try_nominal_owner_missing_2026_10_21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/database/bug.spl:444](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_async_mut/database/bug.spl#L444)
- Review rationale: Full companion explicitly limits typed SdnTable workaround to nominal-owner preservation without claiming producer success. Current update_bug keeps typed get_table_mut? binding and writeback. Inventory-to-target diff adds investigation-log method/import only, not Try owner repair; conservative original validity remains uncertain.

## p4p2_cfg_false_multiline_use_closing_brace_leaks_2026-10-20 — A false @cfg on a multi-line use whose closing brace is alone at column 0 leaks the brace into the parse under the deployed phase-2 producer; gated uses kept single-line (@workaround)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#p4p2_cfg_false_multiline_use_closing_brace_leaks_2026-10-20`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/p4p2_cfg_false_multiline_use_closing_brace_leaks_2026-10-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/p4p2_cfg_false_multiline_use_closing_brace_leaks_2026-10-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_preprocessor.spl:766](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser_preprocessor.spl#L766); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/frontend/when_block_target_cfg_spec.spl:169](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/frontend/when_block_target_cfg_spec.spl#L169)
- Review rationale: Current preprocessor consumes the line closing excluded declaration brackets and clears skip state; regression asserts exactly one active use closer and retained following declaration for both targets. This is the reported merged local parser root remedy; producer/native execution remains untested.
- Review corrections: validity: uncertain -> valid; structural_change: unknown -> no; recommended_action: keep_open -> fixed_pending_verification

## p4p2_cfg_skip_swallows_next_multiline_decl_2026-10-20 — cfg preprocessor counts the next declaration's header bracket before ending a false-@cfg skip, swallowing _map_user_process_image under the deployed producer (@workaround)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#p4p2_cfg_skip_swallows_next_multiline_decl_2026-10-20`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/p4p2_cfg_skip_swallows_next_multiline_decl_2026-10-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/p4p2_cfg_skip_swallows_next_multiline_decl_2026-10-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_preprocessor.spl:773](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser_preprocessor.spl#L773); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/frontend/when_block_target_cfg_spec.spl:184](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/frontend/when_block_target_cfg_spec.spl#L184)
- Review rationale: Current skip logic tests dedent before adding next-header brackets when no excluded bracket is open; regression preserves b(x) following false cfg and checks subsequent declarations. This fixes swallowed next function locally; producer rebuilt from repair still requires qualification.
- Review corrections: validity: uncertain -> valid; structural_change: unknown -> no; recommended_action: keep_open -> fixed_pending_verification

## p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20 — phase-2 producer emits no object symbol for generic free fns and leaves cross-module calls on the unspecialized name (lld-link: undefined symbol lib.nogc_sync_mut.concurrent.mutex.mutex_new/mutex_unlock); i64 gates mirror mutex_lock_gate

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/p4p2_cross_module_generic_free_fn_not_instantiated_2026-10-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/concurrent/mutex.spl:175](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/concurrent/mutex.spl#L175)
- Review rationale: Full report shows caller references to unspecialized mutex generic names absent in defining object. Current i64 mutex_new_gate/unlock_gate call same runtime providers and avoid generic instantiation. Consumer gates are not monomorphization repair; other struct callers remain outside qualification.
- Review corrections: validity: uncertain -> valid

## p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20 — Self-hosted flat parser synthesizes a zero default only for scalar-element fixed arrays; struct/fn-typed module vars need explicit initializers (@workaround in idt.spl)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/kernel/interrupts/idt.spl:97](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/kernel/interrupts/idt.spl#L97)
- Review rationale: Full report locates scalar-only parser default synthesis for initializer-less fixed arrays and leaves language policy unresolved. Current IDT uses explicit zeroed struct and default-handler initializers. This restores consumer contract while parser/general zero-init requirement stays open.
- Review corrections: validity: uncertain -> valid

## parent_commit_piped_reader_no_reassembly_2026-09-16 — parent_commit_piped_result_reader_v1 does not reassemble split stdout chunks

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#parent_commit_piped_reader_no_reassembly_2026-09-16`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/parent_commit_piped_reader_no_reassembly_2026-09-16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/parent_commit_piped_reader_no_reassembly_2026-09-16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/parent_commit_piped_process.spl:128](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_async_mut/parent_commit_piped_process.spl#L128)
- Review rationale: Full report gives exact split-frame loss, while current reader combines pending+chunk, rebuilds bounded pending state, defers later lines at budget and decodes complete lines before inbox offer. Thus the simple missing-concatenation theory is unsupported today. Historical defect stays valid; current root/remedy remains unknown pending caller mutation/inbox qualification.
- Review corrections: inspection_level: report_reviewed -> source_reviewed

## parse_closure_directory_root_validation_2026-10-05 — Parallel parse closure rejects source directory selectors

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#parse_closure_directory_root_validation_2026-10-05`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/parse_closure_directory_root_validation_2026-10-05.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/parse_closure_directory_root_validation_2026-10-05.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/driver_build/native_entry_closure_receipt.spl:74](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/driver_build/native_entry_closure_receipt.spl#L74)
- Review rationale: Current binding digest validates entry with inventory-member rules but validates source_roots with separate directory-capable canonical-relative rule. It rejects traversal, absolute/drive/backslash, separators and controls while preserving ordered length framing. This directly repairs reported directory rejection without weakening selected-file authority; native qualification pending.
- Review corrections: solution: unknown -> known; structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fixed_pending_verification

## parser_contextual_new_index_2026_10_11 — Contextual new identifier indexing emits unsupported allocation AST

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#parser_contextual_new_index_2026_10_11`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/parser_contextual_new_index_2026_10_11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/parser_contextual_new_index_2026_10_11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/00.common/cache_contract/semantic_facet_manifest_v1.spl:198](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/00.common/cache_contract/semantic_facet_manifest_v1.spl#L198)
- Review rationale: Original new[index] became unsupported allocation AST, distinct from dot access. Current semantic-facet merge helpers rename parameter to new_value before indexing. Historical ARM object success qualifies rename only; contextual allocation-versus-index parser repair remains open.
- Review corrections: validity: uncertain -> valid; inspection_level: metadata_only -> source_reviewed

## pass_scope_enum_owner_projection_2026_10_19 — retain declared record and enum subject before qualified match

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#pass_scope_enum_owner_projection_2026_10_19`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/pass_scope_enum_owner_projection_2026_10_19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/pass_scope_enum_owner_projection_2026_10_19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/60.mir_opt/mir_opt/mod.spl:866](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/60.mir_opt/mir_opt/mod.spl#L866)
- Review rationale: Full report limits mitigation to typed MirPassDescriptor/PassScope projection and qualified variants at two dispatch boundaries. Current source does exactly this after status checks, without enabling inactive passes. Stale active-FsDriver tests are separate; general enum propagation and native behavior remain unqualified.
- Review corrections: validity: uncertain -> valid

## phase1_docstring_trim_start_dispatch_2026_10_12 — Phase1 source doctest inventory cannot dispatch str.trim_start

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#phase1_docstring_trim_start_dispatch_2026_10_12`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/phase1_docstring_trim_start_dispatch_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/phase1_docstring_trim_start_dispatch_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/test_runner/doctest_runner.spl:92](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/test_runner/doctest_runner.spl#L92)
- Review rationale: Current docstring extractor computes indentation from existing trimmed content index (or full whitespace-only length), preserving original body bytes. Full report records focused ASCII/Unicode/blank/trailing-space controls only. This substitutes discovery call shape, not missing trim_start dispatch; whole listing/native qualification remain untested.
- Review corrections: validity: uncertain -> valid; inspection_level: report_reviewed -> source_reviewed

## phase3_global_pool_generic_inference_workaround_2026_10_10 — Global array generic inference fails and typed local control crashes

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#phase3_global_pool_generic_inference_workaround_2026_10_10`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/phase3_global_pool_generic_inference_workaround_2026_10_10.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/phase3_global_pool_generic_inference_workaround_2026_10_10.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/types.spl:1643](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/types.spl#L1643)
- Review rationale: Report describes explicit generic arguments enabling only diagnostic continuation with runtime crash/no objects. Current pool promotion now calls specialized typed _type_pool_promote_root helpers rather than nine explicit generic call arguments. This evolved consumer mitigation does not prove generic inference repaired; historical original defect remains valid.

## positional_brace_dict_payload_parsed_as_struct_field_2026_10_20 — positional `V({text: i64})` payload is read as a named field `text: i64`; spelled Dict<K, V>

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#positional_brace_dict_payload_parsed_as_struct_field_2026_10_20`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/positional_brace_dict_payload_parsed_as_struct_field_2026-10-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/positional_brace_dict_payload_parsed_as_struct_field_2026-10-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/phase_memo_ownership.spl:4](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/phase_memo_ownership.spl#L4)
- Review rationale: Current HirPhaseMemoRoot uses Dict<K,V> positional payloads for five map forms. Full report isolates brace dict payload misread as named scalar field, and distinguishes tuple/function payload parser neighbors. Spelling workaround does not repair positional type parser.

## primitive_api_allow_annotation_unimplemented_2026-08-11 — `@allow(primitive_api)` / `#[allow(raw_unit)]` suppression is documented but never implemented

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#primitive_api_allow_annotation_unimplemented_2026-08-11`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/primitive_api_allow_annotation_unimplemented_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/primitive_api_allow_annotation_unimplemented_2026-08-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl:12](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl#L12); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/fix/rules/impl_/lint_allow.spl:63](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/90.tools/fix/rules/impl_/lint_allow.spl#L63); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/lint_allow_attribute_spec.spl:79](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/lint_allow_attribute_spec.spl#L79)
- Review rationale: Full report corrects dead AST-rule attribution. Current live text rule checks shared file-header and per-declaration allow helpers before reporting; regression asserts positive baseline, suppression, unrelated-rule and post-code negative controls. Mechanism is source-repaired locally; function-body/module AST scopes and historical lint debt are explicitly outside this fix. Current execution remains untested.
- Review corrections: structural_change: unknown -> no; inspection_level: report_reviewed -> source_reviewed

## primitive_api_lint_ac_d1_and_ac_d2_are_contradictory_2026-08-04 — primitive_api lint AC-D1 and AC-D2 demand opposite verdicts on the same signature shape

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#primitive_api_lint_ac_d1_and_ac_d2_are_contradictory_2026-08-04`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/primitive_api_lint_ac_d1_and_ac_d2_are_contradictory_2026-08-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/primitive_api_lint_ac_d1_and_ac_d2_are_contradictory_2026-08-04.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl:129](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl#L129)
- Review rationale: Full report proves signature-only exemption cannot distinguish negate(i64)->i64 from extern-wrapper same signature when assertions differ only by body. Current rule still derives pure-math exemption from parameter plus return types and no body context. A deliberate semantic discriminator is unresolved; this is valid contract inconsistency.
- Review corrections: inspection_level: report_reviewed -> source_reviewed

## process_stdout_result_eof_drain_race_2026_10_12 — Stdout Result facade loses buffered data when child exits

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#process_stdout_result_eof_drain_race_2026_10_12`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/process_stdout_result_eof_drain_race_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/process_stdout_result_eof_drain_race_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/io/process_ops.spl:868](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/io/process_ops.spl#L868)
- Review rationale: Full report traces exited-child pending UTF8/output loss and requires independent stdout drain state. Current SPL facade now queries _process_stdout_state_raw after empty read, not process liveness. Linux owner historical qualification does not cover Windows/other platforms or native SPL facade; coordinated runtime lifetime remedy is known but incomplete.
- Review corrections: solution: unknown -> known; structural_change: unknown -> yes; inspection_level: report_reviewed -> source_reviewed; recommended_action: keep_open -> fix_candidate

## provider_loader_path_digest_toctou_2026-08-16 — provider_admit_dynamic_v1 hashes the declared path then reopens it, so digest is not

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: `input/open_bugs_05.tsv#provider_loader_path_digest_toctou_2026-08-16`; [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/provider_loader_path_digest_toctou_2026-08-16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/provider_loader_path_digest_toctou_2026-08-16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/smf/provider_loader.spl:263](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/smf/provider_loader.spl#L263)
- Review rationale: Current admission hashes path bytes, dlopens the mutable path, then rehashes path after load. Second hash can only detect replacement after initializers may execute. Known root remedy binds hashed bytes and load to one immutable handle/snapshot before code runs, requiring loader/OS ownership contract change.
- Review corrections: validity: uncertain -> valid; solution: unknown -> known; structural_change: unknown -> yes; inspection_level: metadata_only -> source_reviewed; recommended_action: keep_open -> fix_candidate
