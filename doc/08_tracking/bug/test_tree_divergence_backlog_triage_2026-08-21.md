# Duplicate test-tree divergence — triage pass (2026-08-21)

Guard: `scripts/check/check-test-tree-divergence.shs --ref <sha>` (committed content only;
the shared working copy carries other sessions' in-flight test edits and disagrees).

## Honest state

| measurement | before | after this pass |
|---|---|---|
| diverged pairs | 878 | 850 |
| baselined | 814 | 806 |
| NEW (unbaselined) divergence | 65 | 44 |
| fixed-but-still-baselined (stale baseline) | 1 | 0 |
| unallowlisted mirror-only | 4 | 0 |

## Method — provable fast-forward only

Each diverged pair was classified by blob history, not by guesswork:
- **FF** — the shadow (`test/unit`, `test/integration`) blob is byte-identical to an
  ANCESTOR revision of the canonical (`test/01_unit`, `test/02_integration`) file.
  The shadow is provably a stale snapshot; copying canonical over it loses no assertion.
- **REV** — the canonical blob is an ancestor revision of the shadow file: the SHADOW is
  ahead. Canonical is the stale leg. Not auto-reconciled — this changes the tree that is
  documented as canonical, so a human must confirm.
- **FORK** — neither side descends from the other. Genuine parallel authoring; must be
  merged by hand.

## Reconciled in this pass (32 pairs, all canonical -> shadow fast-forwards)

21 newly-diverged FF pairs + 7 baselined FF pairs rewritten from committed canonical
content; 1 baselined pair (`unit:lib/nogc_async_mut/async_host_spec.spl`) verified
byte-identical and dropped from the baseline as stale. Plus 4 specs that existed ONLY in
`test/unit/` (landed by `fb87405c18e`, "land reproducing + class-detection specs from
killed sessions") mirrored into `test/01_unit/`, clearing the mirror-only offenders.
No test was deleted and no baseline was regenerated.

### Baseline lines removed (8, each individually justified above)
- unit:compiler_core/file_class_introspection_spec.spl
- unit:compiler_core/interpreter/match_fallthrough_diagnostic_spec.spl
- unit:compiler_core/keyof_spec.spl
- unit:compiler/lint/required_comment_cli_spec.spl
- unit:lib/common/format_spec.spl
- unit:lib/nogc_async_mut/async_host_spec.spl
- unit:lib/nogc_async_mut/wm/compositor_spec.spl
- unit:lib/nogc_async_mut/wm/input_spec.spl

## Needs a human decision

### 6 REV pairs — canonical is the stale leg
- unit:compiler/lint/riscv_rtl_debuggability_spec.spl
- unit:compiler/lint/wide_public_spec.spl
- unit:lib/http_server/csrf_spec.spl
- unit:lib/nogc_async_mut/http_server/static_compression_cache_spec.spl
- unit:lib/nogc_async_mut/http_server/static_file_compression_cache_spec.spl
- unit:lib/nogc_async_mut/http_server/static_file_handler_compression_spec.spl

### 44 remaining NEW divergences — genuine forks

The bulk is one cluster: ~22 `test/*integration/app/scv_*_spec.spl` pairs where both legs
were edited on 2026-08-17 with different fixes for the same problem (a `SIMPLE_PRELUDE`
compiler-path guard added inline in the shadow vs. a `describe` harness probe in canonical).
Merging these needs the scv author. Full list:
- integration:app/scv_delta_pack_spec.spl
- integration:app/scv_diff_spec.spl
- integration:app/scv_fast_import_safety_spec.spl
- integration:app/scv_gates_spec.spl
- integration:app/scv_git_full_interop_spec.spl
- integration:app/scv_git_interop_spec.spl
- integration:app/scv_langmap_safety_spec.spl
- integration:app/scv_manifest_safety_spec.spl
- integration:app/scv_merge_spec.spl
- integration:app/scv_mvp_spec.spl
- integration:app/scv_network_remote_spec.spl
- integration:app/scv_pack_import_spec.spl
- integration:app/scv_pack_verify_safety_spec.spl
- integration:app/scv_parser_artifacts_spec.spl
- integration:app/scv_parser_binary_spec.spl
- integration:app/scv_parser_cache_spec.spl
- integration:app/scv_parser_incremental_spec.spl
- integration:app/scv_parser_integrity_spec.spl
- integration:app/scv_parser_rebuild_spec.spl
- integration:app/scv_parser_wasm_spec.spl
- integration:app/scv_public_remote_spec.spl
- integration:app/scv_refs_safety_spec.spl
- integration:app/scv_restore_export_safety_spec.spl
- integration:app/scv_storage_interop_spec.spl
- integration:app/scv_storage_manifest_spec.spl
- integration:app/scv_storage_safety_spec.spl
- integration:app/scv_storage_spec.spl
- integration:app/scv_structural_match_spec.spl
- integration:app/scv_tree_file_link_safety_spec.spl
- integration:app/scv_tree_object_safety_spec.spl
- integration:app/scv_wasm_executor_spec.spl
- integration:rendering/vulkan_strict_spec.spl
- unit:compiler/frontend/lexer_dead_stream_forward_progress_spec.spl
- unit:compiler/frontend/lexer_indentation_eof_emits_token_spec.spl
- unit:compiler/frontend/lexer_position_unification_spec.spl
- unit:compiler/frontend/lexer_snapshot_spec.spl
- unit:compiler/hir/module_surface_glob_export_origin_spec.spl
- unit:compiler/hir/module_surface_index_allocation_guard_spec.spl
- unit:compiler/hir/reexport_physical_cache_spec.spl
- unit:compiler/hir/rv32_decode_helper_hir_lowering_spec.spl
- unit:compiler/hir/same_named_package_facade_reexport_spec.spl
- unit:compiler/hir/stage4_hir_value_name_dispatch_spec.spl
- unit:compiler/hir/symbol_table_dict_get_source_spec.spl

### 800 baselined FORK pairs

Unchanged from the 2026-08-08 audit's backlog. Per-file triage, not mechanisable.

## Should the duplicate trees exist at all?

**No.** They are an accident of history, and the 2026-08-08 audit
(`doc/09_report/infra/duplicate_test_tree_divergence_audit_2026-08-08.md`) already
established the facts: `test/unit/` is a 99.9% path-subset of `test/01_unit/` and
`test/integration/` a 100% subset of `test/02_integration/`; only the numbered roots are
documented as canonical (`doc/07_guide/infra/test_layout_traceability.md`); commit counts
run 167 vs 12 and 13 vs 2 in favour of the numbered trees. Both trees are collected by
`bin/simple test` (no exclusion in `discover_all_requested_files`), so a diverged pair
can report two contradictory verdicts for what reads as one spec.

Proposed consolidation (reviewable, NOT done here):
1. Drive NEW divergence to 0 and keep it there (this pass: 65 -> 44).
2. Triage the 806 baselined pairs FF/REV/FORK; fast-forwards are mechanical, forks are not.
3. Once the baseline is empty, delete `test/unit/` and `test/integration/` in one reviewed
   commit and add an exclusion in the test runner so they cannot be re-created silently.
Deleting a whole test tree is explicitly out of scope for an automated pass.
