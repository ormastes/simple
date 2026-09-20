# `bin/simple todo-scan` segfaults after writing `todo_db.sdn` and renumbers every id on each run

- Status: PARTIALLY FIXED (2026-09-17) — destructive renumber fixed and pinned
  by spec; post-write segfault NOT reproduced on the macOS aarch64 seed (see
  § Fix 2026-09-17) and remains open for the deployed aarch64-linux seed
- Found: 2026-09-12
- Component: `src/app/todo_scan/main.spl` (`write_todo_db` ~L290), `doc/08_tracking/todo/todo_db.sdn`, `doc/TODO.md`
- Lane: deployed seed `bin/release/aarch64-unknown-linux-gnu/simple` (2026-09-06 09:59, 50,093,192 B)

## Fix 2026-09-17

The merge half of this bug is fixed in `src/app/todo_scan/main.spl`:

- `main()` reads the committed `todo_db.sdn` and `merge_entries` merges the
  fresh scan with it by a stable key — file path + normalized description,
  never the line number. Matched rows keep their id and every curated field
  (keyword/area/priority/issue/blocked/status/valid); only `file`/`line` are
  refreshed, so line drift self-repairs instead of minting a duplicate row.
- A committed `open` row whose marker vanished is marked `closed` — never
  deleted, never renumbered. Curated non-open rows (`blocked`/`in_progress`/
  `closed`) are preserved as-is: a hand-authored row whose text does not
  appear verbatim in source survives the scan.
- New markers are appended with fresh ids past the committed max; ids are
  never reused.
- Pinned by `test/02_integration/app/todo_scan_stable_merge_spec.spl` (4
  scenarios: curated rows/ids preserved, byte-identical db across two
  consecutive scans, vanished marker flips to closed, drift re-points with id
  kept). All 16 examples green across the four todo_scan specs
  (blocked_status, blocked_status_class, log_modes, stable_merge).

Operation note for the first merged run on the real tree: every `open` row
whose description text is not present in its cited file (stale citations,
mirror-spelling duplicates, hand-authored notes) flips to `closed` in one
pass. That is the intended semantics above, but run it deliberately — fresh
worktree, review the diff as its own commit — not as a side effect of an
unrelated scan.

The segfault half: NOT reproduced on this host. The fixed app ran clean
(exit 0, both files written) on the macOS aarch64 seed
(`bin/simple` → `src/compiler_rust/target/bootstrap/simple`) at 3, 360, and
1200 scanned rows. The original crash was on the deployed
aarch64-unknown-linux-gnu seed (2026-09-06 09:59); re-verify there, under
`SIMPLE_EXECUTION_MODE=interpreter` for a diagnostic, before closing this
row.

## Observation

1. `bin/simple todo-scan` (no dry-run flag exists) found 272 TODOs, wrote `todo_db.sdn`, then **segfaulted (exit 139)** before writing `doc/TODO.md`. The db write is destructive: the whole file is rebuilt from the fresh scan with **renumbered ids**, and the one pre-existing `closed` row was silently dropped — there is no merge with the committed db, so `status`/`blocked` decisions recorded by hand do not survive a scan.
2. Because ids are not stable, any external reference to a todo id (records, plan rows) breaks on every run.

The triage of 2026-09-12 therefore restored the pre-scan db from a backup and closed 43 stale rows by hand (ids kept stable); see the triage receipt in the session scratchpad and the resulting `todo_db.sdn` (open 287 → 244, closed 1 → 44, blocked 7 unchanged).

## Fix direction

- `write_todo_db`: merge with the committed db by a stable key (file path + description hash, not line number), preserve `status`/`blocked`/`valid` of existing rows, append new rows with fresh ids, mark vanished markers `closed` — never renumber.
- Find and fix the crash after the db write (run under the seed with `SIMPLE_EXECUTION_MODE=interpreter` to get a diagnostic; likely the `doc/TODO.md` renderer over the 272-row set).
- Pin both with a spec: two consecutive scans over a fixture tree must yield identical ids; a marker removed between scans flips its row to `closed`; the command must exit 0 and write both files.

## Related

- `.claude/rules/structure.md` "Auto-Generated Docs" (TODOs → `doc/TODO.md`, Todo DB → `todo_db.sdn`, when: `bin/simple todo-scan`)
