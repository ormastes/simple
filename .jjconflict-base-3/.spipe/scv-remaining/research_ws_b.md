# WS-B Research: integrity.spl Split Analysis

**File:** `src/lib/scv/integrity.spl` — 718 lines (800-line guard)
**Date:** 2026-05-15

---

## Current Structure Map

| Group | Functions | Lines | Est. Lines |
|-------|-----------|-------|------------|
| Header + tree helpers | `scv_current_tree_content`, `scv_validate_file_chunk_parts`, `scv_validate_tree_file_link`, `scv_validate_tree_row_object_refs` | 1–82 | 82 |
| Parser validation | `scv_validate_syntax_node`, `scv_parser_lock_hash`, `scv_parser_wasm_magic_ok`, `scv_validate_parser_lockfile`, `scv_langmap_field_safe`, `scv_validate_langmap`, `scv_validate_parser_root_identity`, `scv_validate_parser_index_root_fields`, `scv_validate_parser_index` | 83–276 | 194 |
| View/refs validation | `scv_validate_view_commit_ref`, `scv_validate_bookmark_name`, `scv_validate_current_head`, `scv_validate_view_content`, `scv_validate_current_bookmarks`, `scv_validate_current_workspaces`, `scv_validate_operation_views` | 277–422 | 146 |
| Object index/hash | `scv_object_id_from_path`, `scv_object_index_expected_path`, `scv_object_index_kind_ok`, `scv_object_index_actual_keys`, `scv_validate_object_index`, `scv_expected_object_hash`, `scv_validate_deterministic_object_dir`, `scv_validate_deterministic_object_hashes` | 423–546 | 124 |
| Tree objects | `scv_validate_tree_object_rows`, `scv_validate_tree_objects` | 547–596 | 50 |
| Commit refs | `scv_validate_commit_parent_refs`, `scv_validate_change_refs`, `scv_validate_commit_change_refs` | 597–658 | 62 |
| Entry point | `scv_fsck` | 659–718 | 60 |

---

## Dependency Graph (Internal Calls Only)

```
scv_fsck (entry)
  → scv_current_tree_content            [stays in main]
  → scv_validate_tree_row_object_refs   [tree helpers]
  → scv_validate_tree_file_link         [tree helpers]
  → scv_validate_file_chunk_parts       [tree helpers]
  → scv_validate_parser_index           [parser group]
  → scv_validate_parser_lockfile        [parser group]
  → scv_validate_langmap                [parser group]
  → scv_validate_current_head           [view group]
  → scv_validate_current_bookmarks      [view group]
  → scv_validate_current_workspaces     [view group]
  → scv_validate_operation_views        [view group]
  → scv_validate_commit_parent_refs     [commit group]
  → scv_validate_change_refs            [commit group]
  → scv_validate_commit_change_refs     [commit group]
  → scv_validate_deterministic_object_hashes  [object group]
  → scv_validate_tree_objects           [tree-objects group]
  → scv_validate_object_index           [object group]

scv_validate_parser_index (251)
  → scv_validate_syntax_node            [internal, parser group]
  → scv_validate_parser_index_root_fields [internal, parser group]
  → scv_validate_parser_root_identity   [internal, parser group]

scv_validate_parser_lockfile (134)
  → scv_parser_wasm_magic_ok            [internal, parser group]
  → scv_parser_lock_hash                [internal, parser group; also called at 215 by scv_validate_parser_root_identity]

scv_validate_langmap (179)
  → scv_langmap_field_safe              [internal, parser group]

scv_validate_view_content (299)
  → scv_validate_view_commit_ref        [internal, view group]
  → scv_validate_bookmark_name          [internal, view group]

scv_validate_current_bookmarks (344)
  → scv_validate_view_commit_ref        [internal, view group]
  → scv_validate_bookmark_name          [internal, view group]

scv_validate_current_workspaces (367)
  → scv_validate_view_commit_ref        [internal, view group]
  → scv_validate_bookmark_name          [internal, view group]

scv_validate_operation_views (392)
  → scv_validate_view_content           [internal, view group]

scv_validate_tree_object_rows (547)
  → scv_validate_tree_row_object_refs   [tree helpers — SHARED with scv_fsck]
  → scv_validate_tree_file_link         [tree helpers — SHARED with scv_fsck]

scv_validate_tree_objects (587)
  → scv_object_id_from_path             [object group — CROSS-GROUP CALL]
  → scv_validate_tree_object_rows       [internal]
```

### Key Cross-Group Dependency
`scv_validate_tree_objects` (line 587) calls `scv_object_id_from_path` (line 423, object group).
`scv_object_id_from_path` is also called inside `scv_validate_object_index` (line 454, object group).
Since it has two callers in different potential modules, it must stay in the object module.

**Resolution:** Keep `scv_validate_tree_objects` and `scv_validate_tree_object_rows` in `integrity_object.spl` alongside the object helpers, OR merge them into `integrity_object.spl`. This avoids any leaf-to-leaf import.

---

## Proposed Split

### File: `integrity.spl` (main — ~145 lines)
Keeps: imports, `scv_current_tree_content`, tree-row helpers (22–82), `scv_fsck` (659–718)
Rationale: tree-row helpers are called by both `scv_fsck` inline loop AND `scv_validate_tree_object_rows`; keeping them here avoids a leaf-to-leaf import.

| Function | Current lines |
|----------|---------------|
| `scv_current_tree_content` | 9–21 |
| `scv_validate_file_chunk_parts` | 22–52 |
| `scv_validate_tree_file_link` | 53–73 |
| `scv_validate_tree_row_object_refs` | 74–82 |
| `scv_fsck` | 659–718 |

Est. size: ~145 lines (82 + 60 + imports/header ~5). **Well under 500.**

---

### File: `integrity_parser.spl` (~200 lines)
Contains: parser index, lockfile, langmap, syntax-node validation

| Function | Current lines |
|----------|---------------|
| `scv_validate_syntax_node` | 83–117 |
| `scv_parser_lock_hash` | 118–130 |
| `scv_parser_wasm_magic_ok` | 131–133 |
| `scv_validate_parser_lockfile` | 134–175 |
| `scv_langmap_field_safe` | 176–178 |
| `scv_validate_langmap` | 179–201 |
| `scv_validate_parser_root_identity` | 202–221 |
| `scv_validate_parser_index_root_fields` | 222–250 |
| `scv_validate_parser_index` | 251–276 |

Required imports:
```
use app.io.mod (file_exists, file_read)
use std.nogc_sync_mut.io.file_ops.{file_read_bytes}
use std.scv.core.{scv_parser_index_path, scv_parser_lock_path, scv_parsers_dir, scv_langmap_path, scv_object_ref_safe, scv_metadata_path_safe}
use std.nogc_sync_mut.database.core.{SdnDatabase}
```

---

### File: `integrity_view.spl` (~150 lines)
Contains: bookmark/workspace/view/head validation

| Function | Current lines |
|----------|---------------|
| `scv_validate_view_commit_ref` | 277–284 |
| `scv_validate_bookmark_name` | 285–287 |
| `scv_validate_current_head` | 288–298 |
| `scv_validate_view_content` | 299–343 |
| `scv_validate_current_bookmarks` | 344–366 |
| `scv_validate_current_workspaces` | 367–391 |
| `scv_validate_operation_views` | 392–422 |

Required imports:
```
use app.io.mod (file_exists, file_read, dir_walk)
use std.scv.core.{scv_head_path, scv_bookmarks_path, scv_workspace_path, scv_object_ref_safe, scv_worktree_path_safe}
use std.scv.store.{scv_repo_exists, scv_read_workspace_commit}
```

---

### File: `integrity_object.spl` (~180 lines)
Contains: object index, hash validation, tree-object row validation

| Function | Current lines |
|----------|---------------|
| `scv_object_id_from_path` | 423–432 |
| `scv_object_index_expected_path` | 433–440 |
| `scv_object_index_kind_ok` | 441–443 |
| `scv_object_index_actual_keys` | 444–453 |
| `scv_validate_object_index` | 454–508 |
| `scv_expected_object_hash` | 509–524 |
| `scv_validate_deterministic_object_dir` | 525–536 |
| `scv_validate_deterministic_object_hashes` | 537–546 |
| `scv_validate_tree_object_rows` | 547–586 |
| `scv_validate_tree_objects` | 587–596 |

Required imports (includes tree-row helpers from main, via `std.scv.integrity`):
```
use app.io.mod (file_exists, file_read, dir_walk)
use std.scv.core.{scv_objects_dir, scv_object_path, scv_chunk_path, scv_object_index_path, scv_line_set_contains, scv_worktree_path_safe, scv_object_ref_safe}
use std.scv.store.{scv_hash_text, scv_content_id_for_file}
use std.scv.integrity.{scv_validate_tree_row_object_refs, scv_validate_tree_file_link, scv_validate_file_chunk_parts}
```

Note: `integrity_object.spl` imports from `integrity.spl` (main) for the tree-row helpers. This is the only non-star edge.

---

### File: `integrity_commit.spl` (~65 lines)
Contains: commit parent/change ref validation

| Function | Current lines |
|----------|---------------|
| `scv_validate_commit_parent_refs` | 597–615 |
| `scv_validate_change_refs` | 616–642 |
| `scv_validate_commit_change_refs` | 643–658 |

Required imports:
```
use app.io.mod (file_exists, dir_walk)
use std.scv.core.{scv_objects_dir, scv_object_ref_safe}
use std.scv.store.{scv_object_field, scv_commit_tree}
```

---

## Summary: Line Counts per File

| File | Est. Lines | Under 500? |
|------|-----------|------------|
| `integrity.spl` (main) | ~145 | yes |
| `integrity_parser.spl` | ~200 | yes |
| `integrity_view.spl` | ~155 | yes |
| `integrity_object.spl` | ~185 | yes |
| `integrity_commit.spl` | ~70 | yes |

Total: ~755 (vs 718 source + module headers/imports overhead ~37 lines added)

---

## Import Changes to `integrity.spl` (main)

Add after existing imports:
```
use std.scv.integrity_parser.{scv_validate_parser_index, scv_validate_parser_lockfile, scv_validate_langmap}
use std.scv.integrity_view.{scv_validate_current_head, scv_validate_current_bookmarks, scv_validate_current_workspaces, scv_validate_operation_views}
use std.scv.integrity_object.{scv_validate_deterministic_object_hashes, scv_validate_tree_objects, scv_validate_object_index}
use std.scv.integrity_commit.{scv_validate_commit_parent_refs, scv_validate_change_refs, scv_validate_commit_change_refs}
```

Remove from existing imports (no longer needed in main):
- `scv_parser_index_path`, `scv_parser_lock_path`, `scv_parsers_dir`, `scv_langmap_path` (move to parser module)
- `scv_head_path`, `scv_bookmarks_path`, `scv_workspace_path` (move to view module)
- `scv_object_index_path` (move to object module)
- `scv_read_workspace_commit`, `scv_commit_tree`, `scv_object_field`, `scv_content_id_for_file` (split to sub-modules)
- Keep in main: `scv_objects_dir`, `scv_object_path`, `scv_chunk_path`, `scv_head_path`, `scv_line_set_contains`, `scv_metadata_path_safe`, `scv_object_ref_safe`, `scv_worktree_path_safe`, `scv_repo_exists`, `scv_hash_text`

---

## Circular Import Risk

`integrity_object.spl` imports tree-row helpers from `integrity.spl` (main).
`integrity.spl` imports `scv_validate_tree_objects` from `integrity_object.spl`.
**This is a mutual import — a cycle.** Resolution options:

1. **Preferred:** Move `scv_validate_tree_object_rows` + `scv_validate_tree_objects` into `integrity.spl` (main). They are only 50 lines, keeping main at ~195 lines. Object module stays purely about object-index/hash.
2. **Alternative:** Extract tree-row helpers into `integrity_tree_helpers.spl` (tiny ~82 lines); both main and object import it.

Option 1 is simpler — keep main at ~195 lines (well under 500) and the split becomes a clean star with no cycles.

---

## Revised Clean Star Topology (Recommended)

```
integrity.spl (main ~195 lines)
  contains: current_tree_content, tree-row helpers, tree_object_rows, tree_objects, scv_fsck
  imports: integrity_parser, integrity_view, integrity_object, integrity_commit

integrity_parser.spl (~200 lines) — no imports from other integrity_* modules
integrity_view.spl (~155 lines)   — no imports from other integrity_* modules
integrity_object.spl (~135 lines) — no imports from other integrity_* modules (tree_objects moved out)
integrity_commit.spl (~70 lines)  — no imports from other integrity_* modules
```

Zero leaf-to-leaf dependencies. Zero circular imports.
