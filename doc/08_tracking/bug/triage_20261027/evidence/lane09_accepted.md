# Lane 09 accepted review evidence

Accepted classifications captured: 70. Assessment target: `c0b3ad911f4cb00c0f3550b05baa8d06347d17d0`.

## three_layoutbox_variants_2026-08-10 — Four unrelated `LayoutBox` types across the layout lanes (2026-08-10)

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/three_layoutbox_variants_2026-08-10.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/three_layoutbox_variants_2026-08-10.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/blink/layout/block_flow.spl:106](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/blink/layout/block_flow.spl#L106)
- Review rationale: Report records historical spacing duplication and cross-lane sabotage. Current BoxGeometry nests canonical BoxModel at line119 and constructors populate spacing; container remains BlockFlowBox. This concrete cross-module model remedy addresses duplicated edges; source repair is not present runtime verification.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29 — tier-less `use std.X` picks a module by registration order, silently selecting the wrong

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/tierless_std_import_ambiguity_resolves_by_registration_order_2026-07-29.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:263](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl#L263)
- Review rationale: Report narrows registration-order claim: root lib paths win deterministically. Current loader returns src/relative_path before fixed tier search, and common follows nogc_sync_mut. Thus importer's own tier is not generally preferred. Warning stage and explicit imports do not establish systemwide symbol-identity repair.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## tierless_std_js_imports_resolve_to_root_lib_js_not_common_2026-08-01 — Tier-less `use std.js.*` resolves to `src/lib/js/`, never to the importer's own tier

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tierless_std_js_imports_resolve_to_root_lib_js_not_common_2026-08-01.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/tierless_std_js_imports_resolve_to_root_lib_js_not_common_2026-08-01.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl:263](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/interpreter/module_loader_resolve.spl#L263)
- Review rationale: Sentinel report distinguishes ROOT_js from COMMON and documents partial common/js callsite correction. Current loader still checks root src/lib path before tier fallback; no importing-tier preference appears here. Remaining JS type ownership needs decision; explicit callsite workaround does not repair global lookup.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## tldr_future_static_owner_typeparam_2026_10_25 — tldr future static owner typeparam (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tldr_future_static_owner_typeparam_2026_10_25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/tldr_future_static_owner_typeparam_2026_10_25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/80.driver/cache/reader/tldr_table_v1.spl:61](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/80.driver/cache/reader/tldr_table_v1.spl#L61)
- Review rationale: Current deref constructs concrete Poll<text?> and Future<text?>, bypassing static factories exactly as reported. Historical native workaround execution does not repair generic owner substitution; original factory root remedy remains unknown and current target is untested.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## todo_db_description_drift_false_positive_2026-09-12 — `todo_db.sdn` rows can point at a real line whose comment was reworded to a different topic, defeating literal-text "marker gone" detection

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/todo_db_description_drift_false_positive_2026-09-12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/todo_db_description_drift_false_positive_2026-09-12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/todo_scan/main.spl:431](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/todo_scan/main.spl#L431)
- Review rationale: Report warns rewritten comments can falsely close outstanding editorial work. Current merge keys file plus description and closes any unmatched open row at453; stable IDs do not preserve identity across changed description. Therefore stable-key merge does not itself resolve semantic drift; durable identity policy remains undiagnosed.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## todo_scan_segfaults_after_db_write_and_renumbers_ids_2026-09-12 — `bin/simple todo-scan` segfaults after writing `todo_db.sdn` and renumbers every id on each run

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/todo_scan_segfaults_after_db_write_and_renumbers_ids_2026-09-12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/todo_scan_segfaults_after_db_write_and_renumbers_ids_2026-09-12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/todo_scan/main.spl:408](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/todo_scan/main.spl#L408)
- Review rationale: Current merge preserves IDs/curated fields for matched keys, appends above maximum and retains closed rows, addressing destructive renumbering. Report explicitly leaves Linux post-write segfault open despite macOS seed success. Remaining crash root and current execution are unknown; whole record is not fixed.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## trait_default_inherent_override_duplicate_symbol_2026-10-24 — trait default inherent override emits duplicate symbol

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/trait_default_inherent_override_duplicate_symbol_2026-10-24.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/trait_default_inherent_override_duplicate_symbol_2026-10-24.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl:383](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Items/trait_impl_lowering.spl#L383); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_symbol_table_methods.spl:418](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_symbol_table_methods.spl#L418)
- Review rationale: Current injection detects written methods elsewhere and binds their symbol, addressing duplicate injected default. Symbol name still contains owner and name without trait/arity, so second reported explicit trait/inherent collision is not demonstrated fixed. Source workaround and partial remedy do not justify full fixed status.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## trait_group_with_sugar_status_f5_2026-08-09 — trait-group `with` sugar status remeasured: parser-rejection claim superseded, wiring

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/trait_group_with_sugar_status_f5_2026-08-09.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/trait_group_with_sugar_status_f5_2026-08-09.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/desugar/trait_desugar.spl:170](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/desugar/trait_desugar.spl#L170)
- Review rationale: Report proves with parsing and native supertrait dispatch historically, but separates generated acquisition helper and fn-field native compilation blocker. Current offline generator still emits src.accessor_fn(), nested if val and final group accessor; connecting that text transform to compiler would change trait model, not a justified local fix.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## trait_group_with_sugar_unwired_and_from_aot_if_val_2026-08-09 — trait-group `with` desugar is unreachable and its generated .from() capability check is

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/trait_group_with_sugar_unwired_and_from_aot_if_val_2026-08-09.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/trait_group_with_sugar_unwired_and_from_aot_if_val_2026-08-09.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/desugar/trait_desugar.spl:170](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/desugar/trait_desugar.spl#L170)
- Review rationale: Original unwired-desugar and universal if-val claims are narrowed by companion F5 report: native trait groups work, acquisition helper remains separate and fn-field case fails before execution. Current generator still calls accessor fn fields and emits if val; no evidence compiler-side acquisition is repaired.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## transport_profile_sdn_path_cwd_dependent_2026-09-01 — Transport-profile checks fail silently-plausibly when run from any cwd but the repo root

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fix_candidate`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/transport_profile_sdn_path_cwd_dependent_2026-09-01.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/transport_profile_sdn_path_cwd_dependent_2026-09-01.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simpleos_nvme_fw/fw/nvme_transport_config.spl:18](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/09_embedded/simpleos_nvme_fw/fw/nvme_transport_config.spl#L18)
- Review rationale: Current PROFILE_SDN remains repo-relative and loader passes it directly to file_read_text at96. Report's same-tree different-cwd failures support path resolution cause. Local module/repository anchored path resolution plus explicit load error addresses this cause without weakening fail-closed validity.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## tree_size_guard_bands_every_commit_against_one_base_2026-08-17 — `check-tree-size-push` bands every commit against ONE base, so any long legitimate range fails

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/tree_size_guard_bands_every_commit_against_one_base_2026-08-17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/tree_size_guard_bands_every_commit_against_one_base_2026-08-17.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-tree-size-push.shs:495](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-tree-size-push.shs#L495)
- Review rationale: Current reference_for_rev uses each commit first parent, root sentinel and tip-only explicit count; merge branch compares closest parent's count, addressing report's later first-parent merge residual too. Inventory-to-target diff is empty for script. Historical defect remains valid; no current selftest executed.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## u64_range_for_loop_checksum_mismatch_2026-05-14 — u64 range for-loop checksum is correct again but the lane remains materially slower than

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/u64_range_for_loop_checksum_mismatch_2026-05-14.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/u64_range_for_loop_checksum_mismatch_2026-05-14.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/50.mir/mir_lowering_stmts.spl:4079](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/50.mir/mir_lowering_stmts.spl#L4079)
- Review rationale: Current lower_for_range uses has_type_ on flat bound HirType and lower_type for loop_ty; typed default constants replace unconditional i64. This directly implements checksum repair; inventory diff empty. Historical performance parity remains open and current runtime is untested; do not claim performance completion.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## udp_send_to_rejects_typed_u8_array_2026-07-04 — Bug: extern calls taking `[u8]` reject a genuinely-typed `[u8]` array — "byte array element must be integer, got u8"

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/udp_send_to_rejects_typed_u8_array_2026-07-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/udp_send_to_rejects_typed_u8_array_2026-07-04.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/native_io_helpers.rs:133](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/native_io_helpers.rs#L133)
- Review rationale: Current extract_bytes accepts UInt width8 alongside Int, rejects wider unsigned values, and includes positive typed-byte and width16 negative tests. This exactly remedies reported marshaling rejection; inventory diff empty. No seed execution performed and typed transport end-to-end qualification remains pending.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## ui_backend_isolation_gate_name_based_false_positives_2026-08-27 — `check-ui-backend-isolation.shs` flags in-repo Simple functions whose NAME starts with `rt_` (2026-08-27)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ui_backend_isolation_gate_name_based_false_positives_2026-08-27.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/ui_backend_isolation_gate_name_based_false_positives_2026-08-27.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/check/check-ui-backend-isolation.shs:81](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/check/check-ui-backend-isolation.shs#L81)
- Review rationale: Current gate still includes rt-name call regex, matching report's locally defined Simple rt_hal calls by spelling. Comment/string stripping addresses a different false-positive class; declaration provenance requires checking local/imported definitions. Root implementation and scoping needed before labeling remedy local or known.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## ui_c1_unit_nil_type_aliases_native_2026_10_16 — 0CD6 recognizes canonical lowercase unit; capital nominal alias is unresolved

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ui_c1_unit_nil_type_aliases_native_2026_10_16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/ui_c1_unit_nil_type_aliases_native_2026_10_16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/ui.web/bounded_channel.spl:36](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/ui.web/bounded_channel.spl#L36)
- Review rationale: Current try_send uses Result<unit,OverflowError> under explicit 0CD6 workaround marker, matching Ok(()) contract. This repairs source compatibility at this site but does not establish compiler uppercase alias support or complete UI closure; no qualified producer regression receipt.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## ui_scene_route_owner_lookup_ignores_producer_scope_2026-08-08 — ui_scene_route_event resolves owners by a producer-private id with no producer scope, so

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/ui_scene_route_owner_lookup_ignores_producer_scope_2026-08-08.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/ui_scene_route_owner_lookup_ignores_producer_scope_2026-08-08.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/ui/ui_scene_event_route.spl:60](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/ui/ui_scene_event_route.spl#L60)
- Review rationale: Current route looks up first semantic_id match globally, then checks that owner's generation against hit command. It never includes producer scope, reproducing static collision mechanism described. Fix must carry owner/producer identity from assembler/hit through routing contract; exact data-model choice and runtime qualification remain open.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## unsafe_block_expression_binding_parser_gap_2026-08-21 — Unsafe block expression binding parser gap

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unsafe_block_expression_binding_parser_gap_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/unsafe_block_expression_binding_parser_gap_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:537](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl#L537); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:597](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser_stmts.spl#L597); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:1325](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl#L1325)
- Review rationale: Current primary expression parser calls unsafe-block parser, which consumes colon/block and retains capabilities; HIR lowering validates names and stores them on body. This directly repairs expression-position recognition. Interpreter/JIT/native parity and no-runtime-cost evidence remain untested.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## unsafe_block_expression_rhs_2026-08-22 — Unsafe capability block cannot initialize a value

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unsafe_block_expression_rhs_2026-08-22.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/unsafe_block_expression_rhs_2026-08-22.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:537](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl#L537); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:671](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser_stmts.spl#L671)
- Review rationale: Current primary parser recognizes unsafe/danger before generic identifier call and emits block expression with caps. Thus source mechanism rejecting RHS colon has a concrete remedy already. Runtime tail-value and backend parity still require qualified execution; original historical defect remains valid.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## unsafe_capabilities_block_unsupported_in_expression_position_2026-08-30 — `unsafe(capabilities: [...])` is a STATEMENT-only form; in expression position it silently becomes a call and breaks LLVM codegen

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unsafe_capabilities_block_unsupported_in_expression_position_2026-08-30.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/unsafe_capabilities_block_unsupported_in_expression_position_2026-08-30.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:537](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl#L537); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:597](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser_stmts.spl#L597); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:1325](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl#L1325)
- Review rationale: Current RHS parser recognizes unsafe block before ordinary call, preventing capabilities ffi from becoming an undeclared global in described shape. Lowerer validates cap names. Source fixes statement-only mechanism; no Windows LLVM rebuild or negative malformed-syntax evidence claimed.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## unsafe_capabilities_not_carried_into_hir_2026-08-21 — `unsafe` capabilities and reason never reach HIR

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unsafe_capabilities_not_carried_into_hir_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/unsafe_capabilities_not_carried_into_hir_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_definitions.spl:822](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_definitions.spl#L822); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:1325](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl#L1325); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:633](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser_stmts.spl#L633)
- Review rationale: Current HirBlock carries unsafe_caps and lowering validates/stores capabilities, correcting original body-only-loss premise for lexical grants. Parser consumes reason string without storing it in inspected helper, and full declaration annotation propagation not established. Whole reason-plus-capabilities claim remains partially resolved, not invalid.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## unsafe_capability_block_syntax_not_parsed_2026-08-21 — `unsafe(reason: ..., capabilities: [...]):` block syntax does not parse as an unsafe block

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/unsafe_capability_block_syntax_not_parsed_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/unsafe_capability_block_syntax_not_parsed_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/parser_stmts.spl:597](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/parser_stmts.spl#L597); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:1325](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl#L1325)
- Review rationale: Current contextual parser handles reason/capability argument list then emits expr_unsafe_block_with_caps, and HIR constructs UnsafeBlock while carrying caps. This specifically fixes block syntax becoming ordinary expression. No current HIR fixture execution or safety-pass parity result.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25 — untyped val if expr struct boxed as int dict key (workaround registered)

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/untyped_val_if_expr_struct_boxed_as_int_dict_key_2026-10-25.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/20.hir/hir_lowering/_Items/module_build.spl:570](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/20.hir/hir_lowering/_Items/module_build.spl#L570)
- Review rationale: Current fn_key explicitly annotates SymbolId before dictionary insertion under workaround marker. Report isolates call-arm if merge mis-typed as i64 and double boxing; typed callsite prevents symptom but does not establish general untyped-if inference repair. Underlying compiler remains unqualified.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## url_decode_percent_escapes_never_decode_2026-08-18 — `url_decode` never decodes `%XX` escapes

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/url_decode_percent_escapes_never_decode_2026-08-18.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/url_decode_percent_escapes_never_decode_2026-08-18.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/http_client/types.spl:64](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_async_mut/http_client/types.spl#L64); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/http_client/types.spl:64](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/http_client/types.spl#L64); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/http/url.spl:143](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_async_mut/http/url.spl#L143); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/http/url.spl:143](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/http/url.spl#L143); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/lib/http_client/url_decode_percent_spec.spl:8](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/lib/http_client/url_decode_percent_spec.spl#L8)
- Review rationale: Both client facades now delegate to matching HTTP URL owners. Owners accumulate decoded octets then UTF8-decode once, preserving invalid triplets/truncations; spec asserts both profiles,UTF8,NUL,one-layer and long input. Target changes15793feeae3/5a45773c6b7 replace old Option.to_char code; no current test run.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## use_list_names_never_checked_2026-08-04 — The braced name list in a `use` declaration was never checked

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/use_list_names_never_checked_2026-08-04.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/use_list_names_never_checked_2026-08-04.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler/10.frontend/core/interpreter/module_loader_core.spl:650](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler/10.frontend/core/interpreter/module_loader_core.spl#L650)
- Review rationale: Current selective loader loads owner first and binds requested names even when already loaded, fixing old global-name fast-path leak. warn_unprovided_use_names still returns success on loaded owner; noncritical unresolved-module fallback can accept globally available names. Reporting/ownership repair is not full strict use-list contract.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## value_access_ownership_spec_never_executes_2026-09-18 — The compiler runtime-value-accessor ownership spec has never executed, and it is hiding a contradiction with the audit script that replaced it

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/value_access_ownership_spec_never_executes_2026-09-18.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/value_access_ownership_spec_never_executes_2026-09-18.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler/mir/value_access_ownership_spec.spl:3](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler/mir/value_access_ownership_spec.spl#L3); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/audit/compiler-mir-method-sffi-authority.shs:10](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/audit/compiler-mir-method-sffi-authority.shs#L10)
- Review rationale: Current spec imports canonical value_access and demands absence of raw discriminant from method dispatch, while current shell authority guard demands exactly one raw declaration/call. This confirms incompatible ownership assertions persist. Canonical facade object read/search yielded no implementation; owner decision needed before moving or softening guard.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## value_spec_calls_undefined_value_kind_consumers_source_2026-09-06 — `value_spec.spl` calls a helper that is defined nowhere, so one `it` is permanently RED

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/value_spec_calls_undefined_value_kind_consumers_source_2026-09-06.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/value_spec_calls_undefined_value_kind_consumers_source_2026-09-06.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/01_unit/compiler_core/interpreter/value_spec.spl:16](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/01_unit/compiler_core/interpreter/value_spec.spl#L16)
- Review rationale: Current missing helper is defined and reads concrete core/type_checker.spl; assertion now checks canonical import plus val_get_kind(value_id), preserving meaningful consumer invariant. This addresses undefined-helper failure without dropping example. Current spec execution remains pending.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## vhdl_manifest_selfhosted_test_runtime_misrouted_2026-08-12 — VHDL manifest verification is blocked by a bootstrap-seed runtime

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vhdl_manifest_selfhosted_test_runtime_misrouted_2026-08-12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/vhdl_manifest_selfhosted_test_runtime_misrouted_2026-08-12.md)
- Review rationale: Report is explicitly runtime-provenance blocker: seed source resolution pointed elsewhere and cannot attest manifest changes. Root reports qualified full CLI still unavailable, final bounded build failing OS imports. Keep current untested; no fresh VHDL outcome or no-defect conclusion follows from unavailable runner.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## vulkan_device_dispatch_ignores_stencil_mask_2026-08-19 — Vulkan device-dispatch primitives ignore the active stencil mask

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_device_dispatch_ignores_stencil_mask_2026-08-19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/vulkan_device_dispatch_ignores_stencil_mask_2026-08-19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:1397](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl#L1397)
- Review rationale: Current draw_line axis-aligned fast path directly dispatches rectangle shader with clip constants and no mask admission despite rect/list mask fallbacks elsewhere. Thus partial rect repair does not eliminate reported primitive class. Concrete all-primitive mask ownership solution still needs kernel/host parity design and readback evidence.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## vulkan_feature_build_e0252_duplicate_import_2026-08-19 — simple-runtime fails to compile with `--features vulkan --no-default-features` — E0252 duplicate imports

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_feature_build_e0252_duplicate_import_2026-08-19.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/vulkan_feature_build_e0252_duplicate_import_2026-08-19.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/vulkan_graphics_runtime_shader.rs:348](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/runtime/src/vulkan_graphics_runtime_shader.rs#L348); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs:933](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs#L933)
- Review rationale: Top imports are cfg(feature=vulkan), lower duplicate imports cfg(not(feature=vulkan)); mutually exclusive conditions now remove original E0252 mechanism in both files. This is local exact root correction, not invalid original failure. Feature build unexecuted in this review.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## vulkan_icd_virtio_and_gpu_probe_report_no_real_device_enumeration_2026-08-11 — vulkan_icd_virtio and gpu_vendor_probe report no real device enumeration data

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_icd_virtio_and_gpu_probe_report_no_real_device_enumeration_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/vulkan_icd_virtio_and_gpu_probe_report_no_real_device_enumeration_2026-08-11.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl:83](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl#L83)
- Review rationale: Current _venus_device_available returns false; send exits Unavailable before counter-based success branch, so fabricated success is prevented. Real transport/enumeration still absent in this owner and vendor adapters remain separate. Fail-closed correction supports keeping tracked missing device capability open.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## vulkan_no_wait_pending_submission_blocks_followup_compute_2026-09-09 — Vulkan no-wait submission blocks the next compute command

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/vulkan_no_wait_pending_submission_blocks_followup_compute_2026-09-09.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/vulkan_no_wait_pending_submission_blocks_followup_compute_2026-09-09.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs:158](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/runtime/src/vulkan_graphics_runtime_compute.rs#L158)
- Review rationale: Current begin_compute refuses any nonempty quarantined_compute and also checks separate async-session ownership. Legacy no-wait push stores wait_handle while zero denotes unknown completion. Report's sustained legacy ring blockage remains supported; repair requires explicit submission lifecycle/owner contract, not copied Simple handle arrays.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## web_geometry_differ_li_reparented_desyncs_nth_paths_2026-09-13 — Geometry differ: list items are reparented, desyncing every later nth-path

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_geometry_differ_li_reparented_desyncs_nth_paths_2026-09-13.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/web_geometry_differ_li_reparented_desyncs_nth_paths_2026-09-13.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl:48](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl#L48)
- Review rationale: Current list-item scope search stops at special-element barrier before finding an outer li; li/dt/dd callers use it. This prevents nested ul popping outer item and cascading ordinal parent shifts, correcting report's initial differ attribution. Inventory-to-target path unchanged; runtime geometry parity remains untested.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## web_paint_wallclock_budget_flake_2026-07-31 — Web paint path aborts on a wall-clock deadline, making every pixel-verifying spec

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_paint_wallclock_budget_flake_2026-07-31.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/web_paint_wallclock_budget_flake_2026-07-31.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl:612](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_foundation.spl#L612)
- Review rationale: Current budget compares monotonic clock with deadline and latches degraded on expiry; source still has load-dependent abort mechanism documented by same-tree pixel changes. Need policy for deterministic test work and degradation handling; raising environment deadline alone does not remove flake cause.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## web_request_port_evidence_authenticity_2026-08-25 — Web request-port evidence authenticity gap

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_request_port_evidence_authenticity_2026-08-25.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/web_request_port_evidence_authenticity_2026-08-25.md)
- Review rationale: Complete report rejects arbitrary executable/signature-only receipt as server socket proof and requires source/compiler/build/PID/socket/lifecycle binding with unsigned evidence first. This is an unresolved evidence contract needing cross-producer verifier ownership; no current kernel-observed receipt supplied, no invalidity or known implementation claimed.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## web_showcase_dom_tab_bridge_gap_2026-09-05 — Native showcase DOM tab bridge gap

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_showcase_dom_tab_bridge_gap_2026-09-05.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/web_showcase_dom_tab_bridge_gap_2026-09-05.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/web/browser_session.spl:1814](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/web/browser_session.spl#L1814)
- Review rationale: Current generated __simple_dom_matches handles ID,class,tag only; attribute selectors in role-tab fixture still cannot match. Installer only defines style methods in inspected bridge. Native reducer/attribute adapter does not establish generic DOM selector/setAttribute/focus parity or interactive execution.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## web_style_cascade_apply_decls_reparses_per_node_2026-09-12 — The style cascade re-parses declaration text per node: 86% of the cold document pipeline (2026-09-12)

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_style_cascade_apply_decls_reparses_per_node_2026-09-12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/web_style_cascade_apply_decls_reparses_per_node_2026-09-12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:779](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl#L779)
- Review rationale: Current cascade memo key includes inherited parent identity,tag,nested-list state,em base,writing mode,viewport,presentational and merged declarations; hits copy style and misses apply/store. Empty presentational calls also gated at529. This addresses repeated text application with inheritance-aware key; current perf/correctness execution pending.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## web_tab_bar_flex_item_widths_fractional_font_size_2026-09-14 — tab-bar flex items are 1-2 px narrow — fractional UA font-size, not flex (2026-09-14)

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_tab_bar_flex_item_widths_fractional_font_size_2026-09-14.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/web_tab_bar_flex_item_widths_fractional_font_size_2026-09-14.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl:1320](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl#L1320); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl:21](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl#L21)
- Review rationale: Current UA constant is integer13 and Style.font_size i32, while report measures Chrome13.3333 and cumulative item-width error. Fractional font support needs model/measurement contract across style and shaping, not constant nudge. Exact corrected pipeline and runtime comparison remain unqualified.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## web_ui_facade_lib_compile_error_node_types_2026-09-16 — web_ui facade spec blocked: lib compile error in common/web/node_types.spl

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/web_ui_facade_lib_compile_error_node_types_2026-09-16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/web_ui_facade_lib_compile_error_node_types_2026-09-16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/web/node_types.spl:65](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/web/node_types.spl#L65)
- Review rationale: Current Element still declares namespace:text and constructor fills it, matching report site. Report only hypothesizes reserved name/checker mismatch; source shape cannot prove syntax illegal. Keep historical pre-example failure valid, root unknown and current untested pending exact checker diagnostic.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## websocket_timestamp_owner_and_entropy_2026_10_16 — undefined Platform timestamp owner; historical timestamp units unknown

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/websocket_timestamp_owner_and_entropy_2026_10_16.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/websocket_timestamp_owner_and_entropy_2026_10_16.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/websocket/handshake.spl:249](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/websocket/handshake.spl#L249); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/websocket/frame.spl:29](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/websocket/frame.spl#L29)
- Review rationale: Both generators now resolve clock but derive seed=time%256 and deterministic byte products, retaining at most256 nonce/mask states. Real entropy must propagate failure through return/caller contracts; clock substitution is explicit compilation workaround, not security root repair or historical-unit equivalence.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## widget_draw_ir_panel_title_not_rendered_2026-08-09 — Panel titles are never emitted by the pixel Draw-IR pipeline, so titled panels look

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/widget_draw_ir_panel_title_not_rendered_2026-08-09.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/widget_draw_ir_panel_title_not_rendered_2026-08-09.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/ui/widget_draw_ir.spl:517](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/ui/widget_draw_ir.spl#L517); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/ui/layout.spl:73](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/ui/layout.spl#L73)
- Review rationale: Current fallback container/panel emission only adds background rect while panel layout uses inner_y=sy+1. This matches missing title plus no reserved title-row problem. Need choose compatible border/title geometry and tests; simply adding text risks overlap, so no known single remedy asserted.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## windows_collector_named_file_digest_escape_2026_10_12 — Windows collector rejects GNU escaped filename digest

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_collector_named_file_digest_escape_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/windows_collector_named_file_digest_escape_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-logged-process.shs:21](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-logged-process.shs#L21)
- Review rationale: Both helper hash and retained log comparison now feed sha256sum via stdin, removing escaped filename prefix while keeping digest equality checks. Complete report includes historical native Job receipt and wrong-digest rejection, not current execution. This addresses digest rendering root; full bootstrap remains unqualified.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## windows_materializer_genuine_symlink_conversion_unsupported_2026_10_12 — Materializer rejects genuine tracked Windows symlinks

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_materializer_genuine_symlink_conversion_unsupported_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/windows_materializer_genuine_symlink_conversion_unsupported_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:741](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L741); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:1565](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L1565)
- Review rationale: Current shell verifies exact HEAD/index symlink target then invokes NormalizeSymlink. Native owner opens reparse itself, verifies symbolic-link tag/relative target and converts under held handles before placeholder processing. Report's no-conversion assertion is stale; inventory-to-target unchanged. Windows execution pending, guards retained.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## windows_native_checkout_symlinks_materializer_contract_2026_10_12 — Windows native checkout violates materializer placeholder contract

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_native_checkout_symlinks_materializer_contract_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/windows_native_checkout_symlinks_materializer_contract_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:1565](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L1565); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:741](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L741)
- Review rationale: Current verified symlink normalization precedes pending-target and hardlink/junction path, removing dependence solely on checkout placeholders. Exact readlink/HEAD/index and native reparse target checks preserve tamper refusal. Narrow CI false-checkout workaround is no longer only source path; complete Windows materialization untested.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## windows_piped_process_cold_handle_growth_2026_10_12 — Windows piped process cold handle growth blocks resource qualification

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_piped_process_cold_handle_growth_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/windows_piped_process_cold_handle_growth_2026_10_12.md)
- Review rationale: Complete report preserves native exit36 and128-to158 handles with plateau, rejecting thread-specific diagnosis and initialization assumption. Missing diagnostic JSON does not erase retained counts. Owner attribution remains unknown; further retry forbidden and current target untested, so keep open without speculative leak fix.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## windows_rt_process_run_cannot_exec_shebang_script_fixtures_2026-09-02 — Windows: `rt_process_run` cannot execute a shebang script, so every `.shs` CLI fixture returns exit -1

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_rt_process_run_cannot_exec_shebang_script_fixtures_2026-09-02.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/windows_rt_process_run_cannot_exec_shebang_script_fixtures_2026-09-02.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/app/llm_caret/claude_cli.spl:489](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/app/llm_caret/claude_cli.spl#L489)
- Review rationale: Both current Claude CLI calls use process_run_script, matching reported shebang-aware mitigation. Report retains raw Windows process direct-script limitation for other callers, with cmd/sh controls proving process spawning works. Facade substitution does not establish generic runtime root fix.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## windows_spipe_gitlink_alias_pending_policy_missing_2026_10_12 — Windows SPipe gitlink aliases omitted from pending policy

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_spipe_gitlink_alias_pending_policy_missing_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/windows_spipe_gitlink_alias_pending_policy_missing_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/windows-materialized-pending-policy.tsv:5](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/windows-materialized-pending-policy.tsv#L5); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/setup/materialize-symlinks-windows.shs:1492](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/setup/materialize-symlinks-windows.shs#L1492)
- Review rationale: Policy now contains all six exact doc aliases to external SPipe targets, and pending_policy_allows checks exact path-tab-target equality. This addresses omission without arbitrary pending-path allowlist broadening. Complete native materialization remains unexecuted.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## windows_terminal_raw_bytes_crlf_translation_2026_10_12 — Windows raw terminal write translates LF and misreports output byte count

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/windows_terminal_raw_bytes_crlf_translation_2026_10_12.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/windows_terminal_raw_bytes_crlf_translation_2026_10_12.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/runtime/runtime_core_io_exports.c:252](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/runtime/runtime_core_io_exports.c#L252)
- Review rationale: Current Windows rt_term_write locks existing stdout FILE,flushes nolock,gets borrowed descriptor handle and loops counted WriteFile; POSIX retains fwrite. This removes CRT text LF expansion while preserving output owner and no global mode mutation. Native UTF8/NUL/short-write/ordering qualification remains pending.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wine_process_tls_dispatch_spec_pre_existing_red_2026-08-27 — wine_process_tls_dispatch_spec pre-existing RED — missing VM write-readback evidence token

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wine_process_tls_dispatch_spec_pre_existing_red_2026-08-27.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wine_process_tls_dispatch_spec_pre_existing_red_2026-08-27.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl:85](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl#L85); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_peb_teb.spl:261](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/wine_peb_teb.spl#L261)
- Review rationale: Current TLS-dispatch spec still requires VMWriteReadback:PEBTEBLayoutBytes while actual write-result evidence appends PEBTEBLayoutVMReadback. Vocabulary mismatch persists statically; require canonical evidence owner decision and producer-to-consumer semantics before changing assertion, never suppress red based on traceability score.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wine_seh_frame_module_missing_2026-07-20 — wine_seh_frame_spec.spl: `common.wine_seh_frame` module does not exist anywhere in src

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wine_seh_frame_module_missing_2026-07-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wine_seh_frame_module_missing_2026-07-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_seh_frame.spl:29](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/wine_seh_frame.spl#L29)
- Review rationale: Current module defines frame constructor and dispatch planner, validates fault gate/policy,process/thread,stack and mapped handler,then returns explicit planned/no-handler-executed evidence. Missing implementation has been supplied; do not classify historical absence invalid or claim native SEH execution. Focused spec qualification pending.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wine_thread_adapter_missing_impl_2026-07-20 — Missing implementation: common.wine_thread_adapter module

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wine_thread_adapter_missing_impl_2026-07-20.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wine_thread_adapter_missing_impl_2026-07-20.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_thread_adapter.spl:14](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/wine_thread_adapter.spl#L14)
- Review rationale: Current module implements six requested exports: required/missing APIs,SFFI mapping,feature string,gate and wait-result gate. Gate rejects missing APIs or unsignaled wait and uses host contract. Missing-module root resolved in source, while actual thread/runtime qualification and spec run remain untested.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wine_vm_write_readback_token_renamed_specs_red_2026-08-26 — Wine VM write-readback evidence token renamed; specs asserting the old token are RED

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wine_vm_write_readback_token_renamed_specs_red_2026-08-26.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wine_vm_write_readback_token_renamed_specs_red_2026-08-26.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/wine_peb_teb.spl:261](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/wine_peb_teb.spl#L261); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl:85](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/test/system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl#L85)
- Review rationale: Current producer uses PEBTEBLayoutVMReadback and at least inspected consumer still asserts older VMWriteReadback token. This supports real contract drift, not missing write execution inference. Canonical vocabulary and complete consumer sweep required before concrete correction; source mismatch is not current execution.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wire_to_bytes_high_byte_utf8_roundtrip_corruption_2026-09-05 — `bytes_to_wire`/`wire_to_bytes` corrupt round trips for byte values >= 0x80

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wire_to_bytes_high_byte_utf8_roundtrip_corruption_2026-09-05.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wire_to_bytes_high_byte_utf8_roundtrip_corruption_2026-09-05.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_async_mut/io/tls_common.spl:58](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_async_mut/io/tls_common.spl#L58)
- Review rationale: Current bytes_to_wire builds character text via tls_hook_byte_char; wire_to_bytes bounds by len(wire) yet indexes char_code_at and masks255. This retains reported byte-count/codepoint-index mismatch shape; original empty-array correction addresses different symptom. Need encoding contract/owner-qualified byte primitive before known safe remedy.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_content_kind_render_runtime_gate_2026-07-29 — DesktopShell.run() still calls render_all() compatibility path instead of shared frame

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_content_kind_render_runtime_gate_2026-07-29.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_content_kind_render_runtime_gate_2026-07-29.md)
- Review rationale: Complete record explicitly separates source content-kind routing from missing admitted native execution and legacy/direct versus hosted GUI producer gaps. Root's unavailable full CLI leaves current untested; unsupported runtime archive/link failure is a real prerequisite, not invalid renderer claim.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_glass_qemu_evidence_contract_p1_2026-07-27_tldr — WM Glass QEMU Evidence Contract P1 Gaps — TLDR

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_glass_qemu_evidence_contract_p1_2026-07-27_tldr.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_glass_qemu_evidence_contract_p1_2026-07-27_tldr.md)
- Review rationale: Complete TLDR states exhausted rejected candidate cycles and missing provenance/supervision/parser/lifecycle contracts, with neither QEMU row admitted. Duplicate companion is valid tracker; no executable artifact supplied or current runtime qualification. Root remedy unknown until canonical evidence owner resolves listed contracts.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_host_external_content_owner_2026-07-29 — Remote application presentation still RED after content_owner scalar fix for external

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_host_external_content_owner_2026-07-29.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_host_external_content_owner_2026-07-29.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/host_compositor_core.spl:811](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/compositor/host_compositor_core.spl#L811)
- Review rationale: Current BrowserRenderer eligibility reads scalar content_owner and frame admission assigns owner, fixing owner_port inference overwrite. Report explicitly keeps remote native server poll,pixel-present and GUI/pixel event receiver gaps. In-process owner probe does not qualify live remote application flow.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_lifecycle_restore_action_does_not_restore_geometry_2026-08-08 — `apply_wm_action_to_lifecycle_windows` "restore" action does not restore window geometry

- Classification: `valid`, `untested`, `known`, structural change `yes`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_lifecycle_restore_action_does_not_restore_geometry_2026-08-08.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_lifecycle_restore_action_does_not_restore_geometry_2026-08-08.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/wm_action_lifecycle.spl:453](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/compositor/wm_action_lifecycle.spl#L453); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/host_compositor_core.spl:3161](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/compositor/host_compositor_core.spl#L3161)
- Review rationale: Current lifecycle state includes maximized/restore fields; maximize stashes only first transition and restore copies geometry then clamps. Hosted adapters carry all fields both directions. This concrete cross-module model repair resolves one-way overwrite; original latent defect remains valid, runtime roundtrip untested.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09 — check-wm-production-fullscreen-evidence.shs still fails; fix 7fa2d06aaa8 not in deployed

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_production_fullscreen_evidence_security_registry_any_field_infer_2026-08-09.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:1667](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/compiler_rust/compiler/src/pipeline/native_project/mod.rs#L1667)
- Review rationale: Current security_registry_sdn_from_sources parses each candidate but at1695 skips any isolated HIR lowering error and may return None. This matches the report's auxiliary-pass workaround for imported ANY fields; it does not demonstrate complete security inventory or production fullscreen qualification. The historical failure is credible, but treating skip-on-error as a proven root fix would be premature; inspect cross-module inventory completeness and admitted native receipts before closure.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_protocol_status_event_symbols_never_implemented_2026-07-28 — 8 WM IPC status/event symbols imported by live code exist in no source file

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_protocol_status_event_symbols_never_implemented_2026-07-28.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_protocol_status_event_symbols_never_implemented_2026-07-28.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/window_protocol/window_protocol.spl:9](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/window_protocol/window_protocol.spl#L9); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/window_protocol/window_protocol.spl:128](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/window_protocol/window_protocol.spl#L128); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/window_protocol/window_protocol.spl:174](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/window_protocol/window_protocol.spl#L174)
- Review rationale: The historical missing-symbol claim is repaired in current source: both event constants, WmStatus/status values, WmCreateResponse/WmFocusEvent and both constructor functions exist. Exact-size create and focus codecs reject invalid status, zero IDs and noncanonical boolean bytes. This is substantive source repair of the named protocol surface, not evidence the original report was invalid; current importer and roundtrip execution remains untested.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_scene_css_render_perf — WM scene CSS pixel render too slow above 10000 px; path capped by

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_scene_css_render_perf.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_scene_css_render_perf.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/compositor/wm_scene.spl:452](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/compositor/wm_scene.spl#L452)
- Review rationale: render_scene_to_backend still caps pure-Simple CSS at10000 pixels, tries Metal layout/readback for larger scenes and otherwise renders direct themed rectangles. This confirms the costly path is bypassed, not optimized. Historical six-second timing is not a current measurement; the root performance owner and meaningful optimization remain unknown pending a qualified same-scene profile.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wm_taskbar_pin_persistence_transaction_2026-07-29 — Taskbar pin rollback fix has no live native persistence evidence; blocked by VFS global

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wm_taskbar_pin_persistence_transaction_2026-07-29.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wm_taskbar_pin_persistence_transaction_2026-07-29.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/desktop/_DesktopShell/shell_workspace_methods.spl:5](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/desktop/_DesktopShell/shell_workspace_methods.spl#L5)
- Review rationale: Read full short report and current extracted DesktopShell owner. pin_app pops all three appended arrays when save fails and restores was_persisted; unpin_app restores all previous arrays plus persistence truth; save failure increments the error counter and returns false. This directly repairs ignored persistence failure. Report's stubbed native closure is rejected evidence and current no-stub runtime verification remains pending.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## world_units_engine_and_generators_modules_missing_2026-08-21 — `std.common.units.engine` and `std.common.units.generators` do not exist — two specs cannot load

- Classification: `valid`, `untested`, `known`, structural change `no`; action `fixed_pending_verification`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/world_units_engine_and_generators_modules_missing_2026-08-21.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/world_units_engine_and_generators_modules_missing_2026-08-21.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/units/engine/unit_expr.spl:55](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/units/engine/unit_expr.spl#L55); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/units/generators/world_units_importers.spl:24](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/units/generators/world_units_importers.spl#L24)
- Review rationale: Both alleged missing modules now contain implementations. Read all parser/importer behavior: catalog aliases and one quotient parse through exact-rational model functions; unknown atoms fail rather than fabricate units; canonical formatting compares value; five importers produce ten attributed rows including ISO numeric840 and UNECE codes, uniqueness checking and SDN rendering. Source resolves missing-module gap; current specs and model execution still require an admitted runtime.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## wp18_taclebench_import_blocked_by_network_fetch_2026-08-07 — WP-18 TACLeBench import blocked: network fetch (`curl`/`wget`) is hard-blocked in this environment

- Classification: `uncertain`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/wp18_taclebench_import_blocked_by_network_fetch_2026-08-07.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/wp18_taclebench_import_blocked_by_network_fetch_2026-08-07.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md:256](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md#L256)
- Review rationale: Read full report and matching WP18 plan entry. The implemented timing model/observed-max/margin core is explicitly separated from the independent TACLeBench corpus import blocked by that session's fetch restrictions. This is an outstanding evidence/input acquisition task, not demonstrated product defect or approved invalid closure. No present network inability is inferred; corpus identity, license/provenance and current accepted import remain to be established.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05 — All X25519MLKEM768 hot-path operations run interpreted; JIT lost on the entire hybrid-KEM

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/x25519mlkem768_jit_fallback_interpreted_execution_2026-08-05.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/os/crypto/x25519_mlkem768/execution_policy.spl:103](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/os/crypto/x25519_mlkem768/execution_policy.spl#L103); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/cuda.spl:88](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/cuda.spl#L88); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/gc_async_mut/crypto_accel/cuda_session.spl:81](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/gc_async_mut/crypto_accel/cuda_session.spl#L81)
- Review rationale: Report distinguishes imported evidence-field inference failure from unresolved CUDA load symbol and interpreter fallback. Current policy still writes evidence.fallback_used; CUDA load_binary is now defined, exported and called by provider, rejecting empty bytes and passing real arrays to native loader. Missing symbol text is not proof of present failure; JIT field inference and symbol-registration linkage remain unproven, so root fix unknown and benchmark receipts cannot be attributed to compiled execution.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## x25519mlkem768_neon_rvv_ntt_not_implemented_2026-08-08 — NEON and RVV ML-KEM NTT candidates are declared but only the AVX2 i32x8 butterfly exists

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x25519mlkem768_neon_rvv_ntt_not_implemented_2026-08-08.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/x25519mlkem768_neon_rvv_ntt_not_implemented_2026-08-08.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/simd.spl:865](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/simd.spl#L865); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/simd.spl:911](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/simd.spl#L911)
- Review rationale: Read full report and batch/receipt implementation. Batch rejects nonmultiples of256 and all non-AVX2 hosts, then invokes only forward/inverse AVX2 kernels; backend reports1 or0 and RVV VLEN counter resets to0. Capability detection alone therefore cannot admit NEON/RVV. Real architecture-specific kernels plus observed execution receipts are structural work; exact implementation and physical-host qualification remain unknown, not an invalid capability report.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## x64_freestanding_char_code_at_dynamic_text — x86_64 freestanding char_code_at mis-decodes at scattered indices on dynamically built

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x64_freestanding_char_code_at_dynamic_text.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/x64_freestanding_char_code_at_dynamic_text.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:917](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c#L917)
- Review rationale: Read full report, including explicit heap-built vs literal shallow-frame distinction. Current rt_string_char_code_at decodes heap handle and uses raw index/raw byte result, while generic char_code_at expects a tagged integer and returns tagged result. Runtime-side bounds checks do not show which ABI native lowering selects for dynamic text. Root dispatch/lowering diagnosis remains unknown; byte-array workaround does not fix it and normalization closure wording is unsupported.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## x86_32_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11 — x86_32 QEMU Release Lineage, Nonce, and Clean-Source Gap

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x86_32_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/x86_32_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11.md)
- Review rationale: Read full report. Historical x86_32 guest FAT32/ELF execution and expected isa-debug-exit1 do not satisfy clean source, pure-Simple compiler lineage or nonce correlation. The report identifies dirty seed-built media and missing per-run correlation as blockers. No current admitted runtime is available and artifacts were not requalified. Retain as release-evidence gap, root implementation unknown until canonical media/runner nonce path and current lineage receipts are reviewed.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## x86_64_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11 — x86_64 QEMU Release Lineage, Nonce, and Clean-Source Gap

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `report_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x86_64_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/x86_64_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11.md)
- Review rationale: Read full report. x86_64 guest execution, fixed heap/stack placement and ELF64-to-ELF32 multiboot packaging are historical behavioral progress; seed provenance, dirty source and absent nonce still invalidate release qualification. Exit1 is expected protocol success, not a POSIX failure to fix. Current clean compiler/media/nonce receipts unavailable; keep evidence gap open without inferring present runtime reproduction or closing from TEST PASSED.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## x86_bootstrap_rust_authority_tuple_recompilation_cost_2026-08-22 — x86 bootstrap Rust authority tuple rebuild delays Stage 2

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/x86_bootstrap_rust_authority_tuple_recompilation_cost_2026-08-22.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/x86_bootstrap_rust_authority_tuple_recompilation_cost_2026-08-22.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:scripts/bootstrap/bootstrap-from-scratch.sh:3573](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/scripts/bootstrap/bootstrap-from-scratch.sh#L3573)
- Review rationale: Report measures four distinct serial Cargo authority tuples, not merely slow stage compilation. Current wrapper retains seed then native-all then no-LTO runtime and separately compiler-backfill builds, with source fingerprint checks before publication. Feature unification and bitcode archive requirements explain why combining invocations can break correctness. Warm reuse gates do not prove clean-build30percent improvement; precise safe caching/compile reuse solution remains unknown pending fingerprint/timing analysis.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## zstd_brotli_encoders_are_stored_only_2026-08-17 — zstd and brotli encoders emit container-only output LARGER than input (310/304 bytes for

- Classification: `valid`, `untested`, `unknown`, structural change `unknown`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/zstd_brotli_encoders_are_stored_only_2026-08-17.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/zstd_brotli_encoders_are_stored_only_2026-08-17.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/compress/zstd.spl:108](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/compress/zstd.spl#L108); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/compression/brotli/encoder.spl:83](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/compression/brotli/encoder.spl#L83); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/compression/brotli/encoder.spl:171](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/compression/brotli/encoder.spl#L171); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/nogc_sync_mut/compression/brotli/encoder.spl:484](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/nogc_sync_mut/compression/brotli/encoder.spl#L484)
- Review rationale: Read report's zstd root correction and newer encoder behavior. Current zstd finds sequences and attempts real compressed blocks; brotli compares raw, literal and LZ77 outputs. Both brotli compressed paths still reject over4 distinct symbols, so reported ten-symbol repetitive input retains a capability gap while title 'never compress' is obsolete. More capable encoder/interop qualification is required; old seed/interpreter ratio receipts are not current proof and fallback negotiation is not root encoder completion.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.

## zstd_fse_compressed_block_deferred_2026-06-15 — zstd_fse_compressed_block_deferred_2026-06-15

- Classification: `valid`, `untested`, `unknown`, structural change `yes`; action `keep_open`.
- Inspection: `source_reviewed`; state: `accepted`.
- Evidence refs: [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:doc/08_tracking/bug/zstd_fse_compressed_block_deferred_2026-06-15.md](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/doc/08_tracking/bug/zstd_fse_compressed_block_deferred_2026-06-15.md); [c0b3ad911f4cb00c0f3550b05baa8d06347d17d0:src/lib/common/compress/typed/zstd_typed.spl:302](https://github.com/ormastes/simple/blob/c0b3ad911f4cb00c0f3550b05baa8d06347d17d0/src/lib/common/compress/typed/zstd_typed.spl#L302)
- Review rationale: Read entire deferral report and current typed decoder branch: ZSTD_BLOCK_COMP returns explicit unsupported FSE error. The common zstd facade's different real decoder/encoder does not repair this typed API. Reverse bitstream, precise FSE state transitions, literal/sequence decode and checksum ownership remain a substantial structural gap. Intentional deferral is not sufficient authorization to invalidate a concrete unsupported-format report; no current execution claimed.
- Review corrections: Independent exact-target reassessment; worker inventory/wrong-checkout or historical results are not current execution. No current reproducibility, invalidity or root-fix claim inherited.
