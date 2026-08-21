# bug-gen reported to truncate unrelated bug records — NOT REPRODUCED; a real lossy-regenerate fail-open was found and fixed

- **Date:** 2026-08-21
- **Component:** `src/app/bug_gen/main.spl` (`simple bug-gen`)
- **Status:** Fixed (hardening); original report **not reproduced**

## Report

`bin/simple bug-gen` was said to have exited 0 while truncating ~170 unrelated
tracked files under `doc/08_tracking/bug/` and deleting
`doc/08_tracking/bug/assignment_rhs_line_continuation_rejected_2026-08-21.md`
outright. The damage was reverted with `git checkout`; nothing was committed.

## Reproduction attempt — negative

A pristine detached worktree was created at the same HEAD
(`git worktree add --detach /mnt/data/worktrees/buggen-repro HEAD`) and
`bug-gen` was run there twice with cwd inside it:

1. `bin/simple bug-gen` — exit 0, `Generated doc/08_tracking/bug/recent_bugs.md (1292 bugs)`
2. `bin/simple bug-gen --db doc/08_tracking/bug/bug_db.sdn -o doc/08_tracking/bug`
   (the exact invocation in `scripts/hooks/pre-commit:78`) — exit 0

After **both** runs, `git status --short` in the repro worktree listed exactly
one entry: `M doc/08_tracking/bug/recent_bugs.md`. None of the 3,030 files in
`doc/08_tracking/bug/` was truncated, and nothing was deleted.

This matches the source: `src/app/bug_gen/main.spl` contains a **single**
`file_write` (line 175 pre-fix) and no delete/unlink of any kind, and the whole
`src/app/bug_gen/`, `src/app/bug_add/`, `src/app/bug_resolve/` and
`src/app/tracking/` tree contains no code that writes or removes a per-record
`.md` file. **Paths are relative to cwd**, so the tool operates on whichever
worktree it is invoked from — it does not reach into the main worktree; that
half of the report is also not a defect.

Conclusion: the ~170 truncations and the deletion were caused by some other
actor (a parallel agent session or an unrelated doc-regeneration tool), not by
`bug-gen`. Left open for whoever finds the real writer.

## Real defect found and fixed (same defect class, one level up)

`load_bugs()` parsed each row of the `bugs` table with
`if fields.len() >= 10: bugs.push(...)` and had **no `else`**. Any row that is
present but does not fully parse was silently discarded, and `recent_bugs.md`
was then regenerated from the surviving subset and written with exit 0 — a
lossy regenerate that silently deletes a real bug from the index, which is the
same "modify what you did not fully parse" hazard the report describes.

Demonstrated on a fixture whose DB carries one good row and one truncated row:

| | exit | index contains the truncated row | index written |
|---|---|---|---|
| pre-fix | 0 | no — silently dropped | yes |
| post-fix | 1 | n/a | no |

Secondarily, `--db` and `-o` were parsed by **nothing**: the pre-commit hook has
passed `--db doc/08_tracking/bug/bug_db.sdn -o doc/08_tracking/bug` since it was
written, and both were silently ignored while hardcoded relative constants were
used instead. A future edit to those hook paths would have had no effect —
exactly the "path join writing the wrong file" hazard.

## Fix

`src/app/bug_gen/main.spl`:

- `load_bugs(db_path)` now returns a `BugLoad { bugs, unparsed_lines }` and
  records the 1-based source line of every bugs-table row that did not parse.
- `main()` **fails closed** when `unparsed_lines` is non-empty: it prints
  `error[bug-gen]: refusing to regenerate from a partial parse: … nothing was
  written`, returns 1, and performs **no** write at all.
- `--db PATH` / `--db=PATH` and `-o DIR` / `--out DIR` are honoured. `-o` names a
  directory and the tool appends only `recent_bugs.md` to it — bug-gen still has
  exactly one `file_write` and no delete, so it can only ever create or update
  its own generated index, never a record file.
- The `bugs`-table end detection was dead code and had to be repaired for the
  fail-closed parse to be usable: it asked `trimmed != ""` inside a branch that
  already required `trimmed == ""`, so `in_table` never reset and every row of
  the following `bug_investigation_logs` / `bug_fix_strategies` tables was fed
  to the row parser. Pre-fix that was invisible (those rows were silently
  dropped); post-fix it made bug-gen report 59 bogus unparsed rows and refuse to
  run on the real, valid database. It now ends the table at the first
  unindented, non-empty, non-comment line, and the real DB regenerates cleanly
  (1292 bugs, same count as pre-fix).

## Regression spec

`test/01_unit/app/bug_gen/bug_gen_does_not_clobber_records_spec.spl`
(mirrored to `test/unit/app/bug_gen/`). Uses a temp fixture directory holding a
hand-written record that is not in the database and a second record with an
unusual body (tab, conflict-marker-like text, no trailing newline), checksums
both, and asserts they are byte-identical after a clean run, after a
partial-parse run, and after an `-o` run. The partial-parse example fails
pre-fix (exit 0, row silently dropped) and passes post-fix (exit 1, nothing
written).
