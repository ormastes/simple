# Refactor: SCV Workstreams C+D+E

## Files Changed

| File | Action | Lines Before | Lines After |
|------|--------|-------------|-------------|
| `src/lib/scv/pack.spl` | Split (v2 section extracted) | 858 | 464 |
| `src/lib/scv/pack_v2.spl` | Created (v2 delta-pack logic) | — | 363 |
| `src/lib/scv/fast_import.spl` | Flush-commit helper extracted | 760 | 716 |
| `src/app/scv/main.spl` | Updated import for pack_v2 | 371 | 372 |

All other files (fast_import_format, store, refs, network_remote, public_remote, delta, maintenance, integrity, working_copy) were under 800 lines with no dead code, no TODO/NOTE/FIXME comments, and consistent naming — no changes needed.

## Changes Made

### 1. Split `pack.spl` → `pack.spl` + `pack_v2.spl`

`pack.spl` was 858 lines (over the 800-line limit). The natural split point was the existing section divider at the v2 delta-pack section. The split:

- `pack.spl` retains v1 pack (write, verify, import), private-sync (export, verify, import), and all shared byte-manipulation helpers (`scv_append_bytes`, `scv_append_text_bytes`, `scv_pack_bytes_line`, `scv_pack_marker_at`, `scv_pack_payload_for_kind`, etc.) that both halves need.
- `pack_v2.spl` gets the v2 delta-compressed pack logic: `scv_pack_payload_v2`, `scv_pack_write_v2`, `scv_pack_verify_v2`, `scv_pack_v2_verify_payload`, `scv_pack_v2_delta_id_exists`, `scv_pack_resolve_object`, `scv_pack_read_object`, `scv_pack_collect_chunk_ids`, `scv_pack_find_delta_base`.

Dead code removed: `scv_pack_v2_collect_ids` had no callers anywhere in `src/` — deleted.

`main.spl` import updated: split the single `use std.scv.pack.{...}` line into `pack` and `pack_v2` imports.

### 2. Extract flush-commit helper in `fast_import.spl`

The "flush pending commit" block appeared 5 times (blank-line end-of-commit, reset, tag, commit-within-commit, end-of-stream). Each was ~20 lines of identical logic: resolve parents, write tree, write commit, push to commit_ids if mark pending, write op, update status_index.

Extracted to `scv_fast_import_flush_commit(root, tree_lines, current_from_mark, current_merge_marks, commit_marks, commit_ids, current_author, current_committer, op_label) -> (text, text, [text])` returning `(new_commit, error_text, updated_commit_ids)`. Removed ~80 duplicate lines.

## Test Results

All 3 integration specs pass with 0 failures:

- `scv_git_full_interop_spec.spl` — 21 examples, 0 failures
- `scv_network_remote_spec.spl` — 17 examples, 0 failures
- `scv_delta_pack_spec.spl` — 8 examples, 0 failures
