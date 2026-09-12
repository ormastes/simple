# `bin/simple todo-scan` segfaults after writing `todo_db.sdn` and renumbers every id on each run

- Status: OPEN (2026-09-12) — found by the todo-db triage lane; not fixed here
- Found: 2026-09-12
- Component: `src/app/todo_scan/main.spl` (`write_todo_db` ~L290), `doc/08_tracking/todo/todo_db.sdn`, `doc/TODO.md`
- Lane: deployed seed `bin/release/aarch64-unknown-linux-gnu/simple` (2026-09-06 09:59, 50,093,192 B)

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
