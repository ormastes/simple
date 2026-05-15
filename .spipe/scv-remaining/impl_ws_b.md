# WS-B Implementation: Split integrity.spl into sub-modules

## Status: COMPLETE (structural split done; tests require parent session to verify)

## What was done

Extracted 719-line `integrity.spl` into 5 files using the Revised Clean Star Topology (zero leaf-to-leaf circular imports):

| File | Lines | Contents |
|------|-------|----------|
| `integrity_parser.spl` | 200 | Parser/syntax validation: `scv_validate_syntax_node`, `scv_parser_lock_hash`, `scv_parser_wasm_magic_ok`, `scv_validate_parser_lockfile`, `scv_langmap_field_safe`, `scv_validate_langmap`, `scv_validate_parser_root_identity`, `scv_validate_parser_index_root_fields`, `scv_validate_parser_index` |
| `integrity_view.spl` | 152 | View/bookmark/workspace/operation validation: `scv_validate_view_commit_ref`, `scv_validate_bookmark_name`, `scv_validate_current_head`, `scv_validate_view_content`, `scv_validate_current_bookmarks`, `scv_validate_current_workspaces`, `scv_validate_operation_views` |
| `integrity_object.spl` | 130 | Object index and hash checks: `scv_object_id_from_path`, `scv_object_index_expected_path`, `scv_object_index_kind_ok`, `scv_object_index_actual_keys`, `scv_validate_object_index`, `scv_expected_object_hash`, `scv_validate_deterministic_object_dir`, `scv_validate_deterministic_object_hashes` |
| `integrity_commit.spl` | 68 | Commit/change reference checks: `scv_validate_commit_parent_refs`, `scv_validate_change_refs`, `scv_validate_commit_change_refs` |
| `integrity.spl` (main) | 195 | `scv_fsck` entry point + tree helpers that stay to avoid cycle: `scv_current_tree_content`, `scv_validate_file_chunk_parts`, `scv_validate_tree_file_link`, `scv_validate_tree_row_object_refs`, `scv_validate_tree_object_rows`, `scv_validate_tree_objects` |

## Import topology (star — no leaf-to-leaf deps)

```
integrity_parser  ← std.scv.core, std.scv.store
integrity_object  ← std.scv.core, std.scv.store
integrity_view    ← std.scv.core, std.scv.store, std.scv.integrity_object (scv_object_id_from_path)
integrity_commit  ← std.scv.core, std.scv.store, std.scv.integrity_object (scv_object_id_from_path)
integrity (main)  ← std.scv.core, std.scv.store, std.scv.integrity_object, std.scv.integrity_parser, std.scv.integrity_view, std.scv.integrity_commit
```

## __init__.spl changes

Added 4 new exports before `integrity.*`:
```
export integrity_parser.*
export integrity_view.*
export integrity_object.*
export integrity_commit.*
export integrity.*
```

## Cycle avoidance

`scv_validate_tree_object_rows` and `scv_validate_tree_objects` were kept in main (not moved to integrity_object) because they call `scv_validate_tree_file_link` and `scv_validate_file_chunk_parts` which live in main. Moving them to integrity_object would have required integrity_object to import from integrity (main), creating a cycle.

## Verification gap

`bin/simple test` produced no output in this subagent environment (binary exits with 0 but makes no writes — confirmed via strace). The structural split is correct per the dependency graph in `research_ws_b.md`. **Parent session must run:**

```bash
bin/simple test test/integration/app/scv_storage_safety_spec.spl
bin/simple test test/integration/app/scv_parser_integrity_spec.spl
```

Expected: 13 + 2 = 15 examples, 0 failures.
