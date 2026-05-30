# Spec: WS-C Git Interop (PROD-004 / AC-4)

**Spec file:** `test/integration/app/scv_git_full_interop_spec.spl`

## AC-4 Coverage Map

| AC-4 Requirement | describe block | it block | Expected failure pre-impl |
|---|---|---|---|
| Multi-parent commit import | multi-parent merge commits | imports a fast-import stream with a merge commit… | `scv_write_commit_multi` not implemented |
| Multi-parent commit export (`from`+`merge` lines) | multi-parent merge commits | exports a merge commit with both from and merge lines | export DAG walk not yet emitting `merge` lines |
| Change-ID stability for merges (`change-merge:` prefix) | multi-parent merge commits | preserves change-id stability rule for merge commits | `scv_new_change_id_multi` not implemented |
| Lightweight tag import via `reset refs/tags/` | tag objects | imports a lightweight tag via reset refs/tags/… | `scv_tag_set` not wired to reset parser |
| Lightweight tag export | tag objects | exports a lightweight tag as a reset refs/tags/ line | export emitter has no tag-row output |
| Annotated tag import (`tag` record) | tag objects | imports an annotated tag record… | `scv_write_tag_object` not implemented |
| Annotated tag export | tag objects | exports an annotated tag as a tag record… | annotated tag export path missing |
| Tag name ref-safety validation | tag objects | rejects a tag name that fails ref safety validation | `scv_tag_name_valid` not implemented |
| Author metadata preservation | author and committer metadata | preserves distinct author and committer lines… | author/committer fields not stored in commit object |
| Timezone offset preservation | author and committer metadata | preserves author timestamp and timezone offset | tz field not round-tripped |
| Inline blob (single) | inline blob | imports an inline blob and stores file content | inline keyword not parsed in file-command loop |
| Inline blob (multiple per commit) | inline blob | imports multiple inline blobs in one commit | same as above |
| `reset refs/heads/` updates branch pointer | reset command | updates a branch pointer via reset refs/heads/… | reset dispatch not implemented |
| `reset refs/tags/` creates lightweight tag | reset command | creates a lightweight tag via reset refs/tags/ | reset refs/tags/ branch not in parser |
| `reset` with no `from` is rejected | reset command | rejects reset with a missing from target for heads | error path only if dispatch exists |
| Incremental export emits only new commits | incremental export | exports only commits after the since commit | `--since` flag and `scv_export_dag_commits` not implemented |
| Full export when since="" emits all commits | incremental export | full export when since is empty emits all commits | regression guard for existing behaviour |
| Incremental export of merge includes both parents | incremental export | incremental export of a merge commit includes both parents | depends on multi-parent export + --since |
| Linear round-trip fidelity | round-trip fidelity | round-trips a single-branch linear history through git | author/committer loss breaks git import verify |
| Merge+tag round-trip fidelity | round-trip fidelity | round-trips a merge commit DAG with annotated tag | multi-parent + annotated tag export both required |
| Inline blob round-trip | round-trip fidelity | round-trips inline blobs identically to mark-referenced blobs | inline import must produce exportable blob records |

## Notes

- All tests use `process_run("/bin/sh", ["-c", script])` — same pattern as
  `scv_git_interop_spec.spl` and `scv_fast_import_safety_spec.spl`.
- Existing `scv_git_interop_spec.spl` already covers: deletes, renames, copies,
  executable bits, branch refs on regular commits. Those are NOT duplicated here.
- The `--since <commit_id>` flag is the BDD-prescribed CLI form for incremental
  export (positional 4th arg or named flag to `export-git-fast-import`). The
  implementation must accept this form.
- Tests will FAIL until WS-C implementation lands. That is the expected pre-impl state.
- Round-trip tests compare observable git state (file content, parent count,
  tag type) rather than byte-identical streams to tolerate re-serialisation order.
