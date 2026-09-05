# WS-C Implementation Notes: PROD-004 Full Git Interoperability

Status: COMPLETE — 21/21 tests passing

## Files Modified

- `src/lib/scv/store.spl` — multi-parent commit infrastructure
  - `scv_write_commit_multi(root, parents: [text], tree, state, author, committer)` — space-delimited parents field
  - `scv_commit_parents(root, commit_id)` — splits parents field on " "
  - `scv_new_change_id_multi(parents, tree)` — hashes change_id with `change_` prefix (required by `scv_object_ref_safe`)
  - `scv_write_tag_object(root, name, target, target_type, tagger, message)` — stores annotated tag under objects/tags/
  - `scv_tag_name_valid(name)` — name safety predicate
  - Fixed `scv_operation_commit_error`: parents split on `" "` not `","` (backward-compat fix)

- `src/lib/scv/refs.spl` — tag storage
  - `scv_tag_set/get/list` — lightweight tags in `{meta_dir}/tags`
  - `scv_tag_annotated_set/get/list` — annotated tag object IDs in `{meta_dir}/tag_objects/`

- `src/lib/scv/fast_import_format.spl` — validation helpers
  - `scv_fast_import_tag_ref_safe`, `scv_fast_import_reset_ref_error`, `scv_fast_import_tag_record_error`
  - `scv_fmt_author_line`, `scv_fmt_committer_line`, `scv_fmt_tag_record`

- `src/lib/scv/fast_import.spl` — complete rewrite
  - Import: multi-parent (from/merge marks), author/committer capture, inline blobs, reset (heads+tags), annotated tag records
  - Export: BFS DAG walk (`scv_export_dag_commits`), deduplicated blobs, from/merge lines, author/committer, lightweight tags as `reset refs/tags/`, annotated tags as `tag` records
  - Critical fix: flush pending commit before `reset`/`tag` records (no blank line required in stream)

- `src/lib/scv/working_copy.spl` — log enhancements
  - `scv_change_derivation_label(parents_field, tree)` — returns `root:{tree}`, `change-parent:{p}`, or `change-merge:{p1} {p2}`
  - `scv_log_branch(root, branch)` — traverses commit DAG and includes derivation in output

- `src/lib/scv/integrity.spl` — bug fix
  - `scv_validate_commit_parent_refs`: split parents on `" "` not `","` (matched store.spl format)

- `src/app/scv/main.spl` — CLI surface
  - `log [branch]` — optional branch arg routes to `scv_log_branch`
  - `export-git-fast-import` — parses `--since <commit>` flag
  - `tag-list`, `tag-set` commands

## Key Design Decisions

1. **Change-ID for merge commits**: `scv_object_ref_safe` enforces `change_` prefix, so merge change IDs are stored as `change_<sha256(change-merge:p1 p2)>`. The human-readable `change-merge:` label appears in `scv_log_branch` output (derivation field), not as the stored ID.

2. **Space-delimited parents**: `parents: id1 id2` format is backward-compatible — single-parent commits continue to work unchanged.

3. **Tag directories on-demand**: `objects/tags/` created by `scv_write_tag_object` only when needed; not part of `scv_init`.

4. **Incremental export**: BFS from head, stops at `since` commit boundary, returns oldest-first ordered list.
