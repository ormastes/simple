# Tracking DB triage — restart plan (2026-09-13)

Goal: every non-done row in `doc/08_tracking/bug/bug_db.sdn` (`bugs`, `bugs_active`)
and `doc/08_tracking/todo/todo_db.sdn` (`todos`) is rechecked against the current
tree and either closed (fixed / stale / invalid) or kept open with fresh evidence.
Scope is **DB files only** — record `.md` files are not edited.

## State

| Step | Status |
|------|--------|
| Pass 1: small-model verify + Opus review, 970 rows | DONE — landed PR #844 (`ae75278524a`) |
| bug_db structural repair (duplicate `bugs_active`/`bugs` blocks, stale 2nd CRC line) | DONE — #844 |
| todo_db id-collision repair (sync `13ca132a222` appended a re-scan with ids restarting at 0) | DONE upstream — `febc47524a4` (pass-1 ids 0..295 preserved, 0 closures reopened) |
| Pass 2 (clean restart, run `wf_0a7c1b6a-a9e`, 890 rows / 37 chunks of 25) | DONE — every row verified and Opus-reviewed (after a spend-limit stop and resume); 162 closures, 159 applied (3 todos already closed upstream) |

Pass-2 verdicts: bugs 113 fixed / 24 stale / 17 invalid / 527 still open;
todos 5 fixed / 1 stale / 2 invalid / 201 still open. Where the first (pre-limit) and
final Opus reviews disagreed, the row stays open (4 rows). Todo rows with ids >= 296
were matched to `origin/main` by (description, file, line), since upstream renumbered them.

After pass 2: bugs 279 fixed / 522 closed / 509 open / 3 pending;
bugs_active 26 fixed / 3 closed / 10 open / 3 pending; todos 143 closed / 184 open / 8 blocked.
A future pass should target only rows whose status is still open on `origin/main`.

## Restart from a clean workflow

1. **Export** the still-open rows from `origin/main` (never the shared working copy):
   `git show origin/main:<db>` into a scratch dir, then emit JSON chunks of ~25 rows.
   Bug items carry id, table, status, severity, title, file, line, reproducible_by,
   created/updated, and the record path `doc/08_tracking/bug/<id>.md` when it exists.
2. **Verify** (one small-model agent per chunk) — per row, verdict
   `still_open | fixed | close_stale | close_invalid` + evidence. Guide:
   - read the record `.md` and the referenced `file:line`; `git log -S`/`--follow` for renames;
   - `fixed` needs a cited commit or current code proving the defect is gone;
   - `close_stale`: referenced file/subsystem removed and no successor, or superseded
     by a newer row/record; age alone is not enough;
   - `close_invalid`: the claim was never true at the cited code;
   - a moved file is not a deleted file; a workaround is not a fix; unsure -> `still_open`.
3. **Review** (one Opus agent per chunk) — re-check every non-`still_open` verdict,
   downgrade weak evidence, and probe a few `still_open` rows that look fixed.
4. **Coverage check** — every exported id has exactly one reviewed verdict.
5. **Apply** on fresh `origin/main` DBs, keyed by id, idempotent:
   - bugs: status -> `fixed` or `closed`, `updated_at` -> apply date; skip rows already
     `fixed`/`closed`/`resolved-duplicate`;
   - todos: status -> `closed`;
   - reseal: `sh scripts/check/reseal-sdn-crc32.shs doc/08_tracking/bug/bug_db.sdn`.
6. **Conflict checks before commit** (both DBs): one block per table name, exactly one
   `#sdn-crc32` line (line 1), CRC matches, 0 duplicate ids, 0 wrong-column-count rows,
   and a sorted diff against `origin/main` shows only status/updated_at changes.
7. **Land**: plumbing commit on `origin/main` (temp `GIT_INDEX_FILE`) touching only the
   two DBs, push `work/<topic>`, `gh pr create`, `gh pr edit` to fire admission, merge
   on `mergeable: MERGEABLE` + `mergeStateStatus` CLEAN/UNSTABLE, delete the branch.

## Watch-outs
- Whole-working-copy sync commits re-introduce stale DB content (both the duplicate
  bug_db blocks and this todo id collision came from that path). Re-run step 6 on
  `origin/main` after any sync lands.
- A bad `bug_db.sdn` CRC makes the whole DB load as nil — always reseal.
- `scripts/check/sync-tracking-db-status.shs` only closes rows from record `.md`
  status; closing a DB row whose record still says open can flag
  `check-bug-status-consistency.shs` — accepted for DB-only scope.
