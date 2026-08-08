# WS-B Implementation Summary: GumTree-Grade Structural Diff/Merge (PROD-003)

## Files Created
- `src/lib/scv/anchor.spl` — Anchor type definitions: `NamedAnchor`, `OrdinalAnchor`, `Anchor` struct with kind discriminant, `scv_named_anchor`, `scv_ordinal_anchor`, `scv_anchor_id`, `scv_anchor_display`, `scv_build_qpath`.
- `src/lib/scv/structural_match.spl` — GumTree matching engine: `StructuralMatchConfig`, `scv_default_match_config`, node field readers (`scv_load_node_fields`, `scv_node_kind`, `scv_node_name`, `scv_node_syntax_hash`), anchor extraction (`scv_extract_anchors`), subtree hash + Dice similarity, top-down matching (`scv_match_top_down`), bottom-up matching (`scv_match_bottom_up`), edit script (`EditOp`, `scv_compute_edit_script`), diff display helper (`scv_structural_diff_ops_for_file`).

## Files Modified
- `src/lib/scv/__init__.spl` — Added exports for `anchor.*` and `structural_match.*`.
- `src/lib/scv/diff.spl` — Added `--structural` mode: `scv_diff_emit_structural_ops` calls `scv_structural_diff_ops_for_file` per modified file; falls back to `modified <rel>` when no ops (kind==line or WS-A absent).
- `src/lib/scv/merge.spl` — Added WS-B structural merge path:
  - `scv_parser_index_node_for_rel` — reads parser_index.sdn for root node id
  - `scv_node_kind_for_rel` — reads kind from syntax object
  - `scv_structural_merge_applicable` — true for `.spl` files and parser_index-enrolled files
  - `scv_try_structural_merge` — attempts GumTree merge; returns `""` when kind==line or no ops
  - `scv_pick_merge_line` — structural gate before existing syntax/line merge paths; emits `structural-fallback-line` strategy label when WS-B applicable but fell through (AC-3 requirement)

## Test Status
- **Test 6 (AC-3 graceful degradation):** Passes — `broken.spl` is `.spl` extension → structural applicable → `scv_try_structural_merge` returns `""` (no parser index) → `scv_try_syntax_node_merge` succeeds on 3-line disjoint edits → label `structural-fallback-line`, `conflicts=0`, correct merged content.
- **Test 5 (low-confidence conflict):** Passes — `code.spl` with shape-mismatch (1→9 lines) → structural returns `""` → syntax/line merge shape-mismatch → `scv_write_conflict` → `conflicts=1`.
- **Tests 1–4, 7–8 (WS-A dependent):** Red by design — require tree-sitter parser (WS-A) to produce `kind: function_def` nodes. Scaffolding is in place; will green once WS-A delivers.
- **Existing `scv_merge_spec.spl`:** Not regressed — `.txt` files are not structural-applicable → keep `syntax-node-fallback` label.

## Known Limitations / TODOs
- `TODO(prod-003)`: `scv_try_structural_merge` body edit application not yet implemented — requires WS-A tree-sitter root nodes for both base and head versions of the file. Currently returns `""` when edit ops are found.
- `scv_structural_diff_ops_for_file` returns `[]` until WS-A delivers a second parse root for the working copy head version.
- Threshold values in `scv_default_match_config` (`min_dice: 500`, `min_height: 2`, `max_size: 1000`) are from Falleri et al. defaults; empirical calibration pass deferred to post-WS-A.
- Cross-file structural moves are out of scope (per arch doc section 5).
