# `todo_db.sdn` rows can point at a real line whose comment was reworded to a different topic, defeating literal-text "marker gone" detection

- Status: OPEN (2026-09-12) — found while building `scripts/check/sync-tracking-db-status.shs`; not fixed here (out of scope for that tool)
- Found: 2026-09-12
- Component: `doc/08_tracking/todo/todo_db.sdn`, `scripts/check/sync-tracking-db-status.shs`
- Binary: n/a (pure text/db defect, not a compiler/runtime defect)

## Observation

`sync-tracking-db-status.shs`'s todo-side heuristic ("row is done when its
`description` text is no longer found anywhere in `file`") was built to
replace `todo-scan`, which is independently known broken (see
`todo_scan_segfaults_after_db_write_and_renumbers_ids_2026-09-12.md`). Two
false-positive classes were found by manual spot-check of its `--dry-run`
output against the real tree:

1. **`line: 1` curated backlog notes** (ids 285, 287-291, 293, 294 in the
   2026-09-12 tree): these are hand-authored summary rows attached to a file
   at line 1, not scanned from a specific comment, so there was never a
   guarantee the description appears literally in that file. `sync-
   tracking-db-status.shs` now treats `line == 1` with no textual match as
   inconclusive and leaves the row untouched — this class is handled.

2. **Reworded-in-place comment at a real, non-1 line** (id 292, **not**
   handled): the row reads
   `file=src/compiler_rust/compiler/src/pipeline/native_project/linker.rs,
   line=622`, description starting "REMOVE every external libsqlite3 link and
   replace it with Simple's embedded DB engine. Owner directive 2026-09-07.
   ...". The actual comment at that file today
   (`grep -n TODO src/compiler_rust/compiler/src/pipeline/native_project/linker.rs`)
   is about `rt_*` symbol link precedence between `native_all` and the core-C
   supplement — a completely different topic. The row's `file`/`line` is
   stale (points at a location whose comment was independently rewritten,
   not removed), not "done" — the underlying sqlite-removal work is very
   much still open (see sibling todo ids 292/293 and the `rt_sqlite_*` bugs).
   A text-presence check has no signal to catch this: there is no tag, no
   quote-only drift, and the line number is real, so it looks exactly like a
   genuinely-removed marker.

## Why this matters

Any tool (this one included) that infers "todo is done" from "its description
text isn't in the file anymore" will misclassify case 2 as done and silently
lose track of real outstanding work — exactly the failure mode
`CLAUDE.md`/`.claude/rules/structure.md` warn about for TODO/FIXME handling.
`sync-tracking-db-status.shs` was deliberately left honest about this (see
"Known limitation" in
`doc/07_guide/infra/tracking/sync_tracking_db_status.md`) rather than papered
over with a broader heuristic that would have hidden more true positives to
catch this one false positive.

## Fix direction

- The real fix is the same one `todo_scan_segfaults...` already calls for:
  re-scan and merge by a stable key (file + description hash), not by
  trusting an old `line` pointer or bare description presence. Until
  todo-scan is fixed and made non-destructive, this class of row cannot be
  mechanically verified and needs a human read before any tool closes it.
- Short term: before applying `sync-tracking-db-status.shs`'s todo changes on
  the real tree, a human should specifically re-check any row whose
  description mentions multiple files/paths or reads as an editorial
  multi-sentence note (not a single short clause) even when its `line` is not
  `1` — id 292 is the concrete instance found so far; there may be others in
  the ~30-row real-tree change set this tool produced on 2026-09-12.
