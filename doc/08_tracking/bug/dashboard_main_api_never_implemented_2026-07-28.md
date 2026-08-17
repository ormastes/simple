# `app.dashboard.main` is a 14-line stub — both dashboard modules import an API that was never written

Status: **OPEN (P2)** — tracked under `dashboard_main_lost_table_model_2026-08-04.md`,
which is ITSELF OPEN. The defect is live and unfixed.

> ~~Status: DUPLICATE of dashboard_main_lost_table_model_2026-08-04.md~~
> ~~Status re-verified 2026-08-17 by source inspection (triage shard 00).~~
> **SUPERSEDED 2026-08-17 — FALSE CLOSURE.** The `DUPLICATE` marker above was
> wrong in effect, not in fact: the row it points at is open, so the tag closed
> this row while nothing was fixed, making a live defect invisible. The
> duplicate RELATIONSHIP is genuine and is retained; only the CLOSURE it implied
> is withdrawn.

## Status correction 2026-08-17 (source inspection only)

**What the status claimed:** closed as a DUPLICATE.

**What was actually verified** (2026-08-17, re-grepped from current working-tree
source; no compiler, test, or build was run — SOURCE INSPECTION ONLY, and the
prior status stamps were treated as claims, not evidence):

- `src/app/dashboard/main.spl` is **87 lines** and defines **0** of the required
  symbols: `grep -c 'DASHBOARD_CACHE_PATH\|TABLE_NAMES\|fn load_table\|fn ensure_dirs'`
  returns `0`.
- Two siblings still IMPORT that missing API:
  - `src/app/dashboard/dashboard_collectors.spl:8` —
    `use app.dashboard.main.{Table, load_table, load_table_named, header_index, get_field, count_eq, sum_int, count_nonempty, write_table, today_date, itos, DASHBOARD_TABLE_DIR}`
  - `src/app/dashboard/dashboard_export_runtime.spl:7` — `use app.dashboard.main.{`
- `doc/08_tracking/bug/dashboard_main_lost_table_model_2026-08-04.md` line 3 reads
  `Status: OPEN (P2)`.

**Corrected to:** OPEN (P2), duplicate-of relationship retained without closure.

**Ownership:** the underlying fix belongs to the `llm-caret` lane via
`dashboard_main_lost_table_model_2026-08-04.md`. This edit changed STATUS ONLY —
no dashboard source was restored or modified here.

### Traps for whoever fixes this later

- **(a) A renamed-away repro proves nothing.** The `ce` repro that used to live
  in `src/app/office/pptx_export.spl` was RENAMED AWAY — `grep -c '\bce\b'` on
  that file is now `0`, the identifiers are `pic_end` (`:526`) and `tce`
  (`:423,424,427,431`). Re-running that file therefore exercises nothing, even
  though the parser fix itself is real and present at
  `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:487-491`.
- **(b) Do not cite `3c4e6551b7a` as the `ce`/`Grid` fix.** That commit
  ("fix(parser): 11 soft keywords could not be used as identifiers") covers
  `auto bind by examples export into lazy mod move on onto requires skip spawn
  unwrap use where with` — verified from its own test file
  `src/compiler_rust/parser/tests/contextual_keyword_identifiers.rs`. Neither
  `ce` nor `Grid` is in it.

**Date:** 2026-07-28 · **Status:** open · **Class:** NEVER-EXISTED (capability gap)
**Found:** triage of `scripts/check/check-dangling-references.shs` findings scoped
to `src/app/dashboard/**`. 16 of the 25 findings in `src/app/{cli,dashboard}`
come from this single defect.

## Symptom

```
src/app/dashboard/dashboard_collectors.spl:8     -- 7 SYMBOL findings
src/app/dashboard/dashboard_export_runtime.spl:7 -- 9 SYMBOL findings
```

## Referencing sites

`src/app/dashboard/dashboard_collectors.spl:8`

```spl
use app.dashboard.main.{Table, load_table, load_table_named, header_index, get_field,
                        count_eq, sum_int, count_nonempty, write_table, today_date,
                        itos, DASHBOARD_TABLE_DIR}
```

Flagged as declared nowhere: `load_table`, `load_table_named`, `header_index`,
`sum_int`, `count_nonempty`, `today_date`, `DASHBOARD_TABLE_DIR`.

`src/app/dashboard/dashboard_export_runtime.spl:7`

```spl
use app.dashboard.main.{
    DASHBOARD_CACHE_PATH, DASHBOARD_HISTORY_DIR, DASHBOARD_TABLE_DIR,
    TABLE_COUNT, TABLE_HEADERS, TABLE_NAMES, current_month, ensure_dirs, ...
```

Flagged as declared nowhere: `DASHBOARD_CACHE_PATH`, `DASHBOARD_HISTORY_DIR`,
`DASHBOARD_TABLE_DIR`, `TABLE_COUNT`, `TABLE_HEADERS`, `TABLE_NAMES`,
`current_month`, `load_table`, `today_date`.

## Missing target

`src/app/dashboard/main.spl` is **14 lines** and declares five functions, none of
which is any of the above:

```
_dashboard_surface_result, _run_serve_result, _run_gui_result,
_run_agents_result, main
```

No table model, no constants, no date helpers. Repo-wide search confirms
`DASHBOARD_TABLE_DIR` appears **only** in the two consuming files, and
`fn load_table` / `fn today_date` / `fn sum_int` / `fn count_nonempty` /
`fn header_index` / `fn load_table_named` / `fn current_month` exist in no
`.spl` file under `src/` or `test/`.

The handful of names on those import lines that the checker did *not* flag
(`Table`, `get_field`, `count_eq`, `ensure_dirs`) are false negatives of the
checker's name-global SYMBOL rule: they resolve against completely unrelated
modules (`src/app/office/database/table.spl`, `src/compiler/70.backend/bitfield.spl`,
`src/lib/hardware/nand_emu/test/scenario_spec.spl`,
`src/app/task_daemon/main.spl`). None of them is the dashboard's.

## Git evidence — NEVER-EXISTED, not a deletion victim

Against the healthy pre-incident tree `6fd7474260c` (parent of `115803a7aff`,
before the jj-conflict-tree push):

```
git grep -l 'DASHBOARD_TABLE_DIR' 6fd7474260c -- 'src/*.spl'
  src/app/dashboard/dashboard_collectors.spl
  src/app/dashboard/dashboard_export_runtime.spl

git cat-file -p 6fd7474260c:src/app/dashboard/main.spl | wc -l
  14
```

`main.spl` was already the same 14-line stub, and the constant appeared only at
the two consuming sites. `git log -S'DASHBOARD_TABLE_DIR' -- src/app/dashboard/`
returns only conflict-tree churn commits (`37cda4befdc`, `3f577c312de`,
`115803a7aff`, …) where the whole subtree appears/disappears — no commit ever
added a definition. **This is not conflict-tree collateral damage.**

## Consequence

`dashboard_collectors.spl` (18 KB) and `dashboard_export_runtime.spl` (9 KB) are
both unresolvable. Neither has an importer outside the pair
(`dashboard_export_runtime.spl` imports `dashboard_collectors.spl`; nothing
imports `dashboard_export_runtime.spl`), so the whole dashboard
collector/export surface is unreachable dead weight today — but it is 27 KB of
written logic, so it is filed as a gap rather than deleted.

## Not fixed here

Two legitimate outcomes, both needing an owner: implement the
`app.dashboard.main` table/constants API that these 27 KB were written against,
or delete both modules as abandoned. Not guessed at here.
