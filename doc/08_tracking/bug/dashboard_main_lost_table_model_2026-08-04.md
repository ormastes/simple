# BUG: `app.dashboard.main` no longer defines the table model its own siblings import

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
is now 3,094 bytes (grown from the originally-reported 382-byte stub, so the
CLI entry-point work continued), but still defines none of the ten table-model
symbols: `grep -c 'DASHBOARD_CACHE_PATH\s*=\|TABLE_NAMES\s*=\|fn load_table\|fn ensure_dirs' src/app/dashboard/main.spl` is 0, and the tree-wide grep from the
original repro still finds no dashboard-specific definition (only unrelated
`ensure_dirs` in other apps). `dashboard_collectors.spl:8` and
`dashboard_export_runtime.spl:7` still `use app.dashboard.main.{...}` those
exact ten symbols — unchanged. Not fixed here: restoring the 26,786-byte
recoverable blob (`2ee3fed72cd8e6538646983b84765c4787fc175a`) is a stdlib-API
port, not a mechanical revert, AND the doc's own "Ownership warning" section
explicitly says this path is active `llm-caret`-lane development and must not
be restored unilaterally by another session. Left honestly open, respecting
that ownership boundary; the recovery path recorded below remains valid and
unclaimed by anyone outside that lane.
**Found:** 2026-08-04
**Severity:** high — two dashboard modules import ten symbols that exist nowhere
in the tree, so every dashboard data path is dead code that still "compiles"

## Symptom

Minimal repro (the symbols are simply absent from the whole source tree):

```sh
/usr/bin/grep -rn 'DASHBOARD_CACHE_PATH\s*=\|TABLE_NAMES\s*=\|fn load_table\|fn ensure_dirs' \
  src/ --include=*.spl
```

Actual: no hit defines any dashboard symbol (`ensure_dirs` matches only
unrelated apps — `task_daemon`, `test_daemon`, `test_runner_new`,
`mcp/assistant`).
Expected: `src/app/dashboard/main.spl` defines them, because two sibling modules
import them from exactly there:

- `src/app/dashboard/dashboard_collectors.spl:8`
  `use app.dashboard.main.{Table, load_table, load_table_named, header_index, get_field, count_eq, sum_int, count_nonempty, write_table, today_date, itos, DASHBOARD_TABLE_DIR}`
- `src/app/dashboard/dashboard_export_runtime.spl:7-11`
  `use app.dashboard.main.{DASHBOARD_CACHE_PATH, DASHBOARD_HISTORY_DIR, DASHBOARD_TABLE_DIR, TABLE_COUNT, TABLE_HEADERS, TABLE_NAMES, current_month, ensure_dirs, load_table, today_date}`

The failure is silent: an unresolved `use` is only a warning, so `simple check`
and the spec suite stay green while `run_export`, `run_snapshot`,
`run_invalidate_cache`, `export_json`, `export_html` and `compute_summary` can
never actually execute.

## Root cause

`src/app/dashboard/main.spl` was truncated to a 382-byte stub and the module
that used to hold the dashboard table model was never restored.

Proved by blob size across history:

```sh
git log --all --format=%h -- src/app/dashboard/main.spl | while read c; do
  s=$(git cat-file -s $(git rev-parse $c:src/app/dashboard/main.spl 2>/dev/null) 2>/dev/null)
  [ -n "$s" ] && echo "$c $s"
done | sort -k2 -n -r | head -3
```

- `289d102ba64` — **49698 bytes** (2026-02-16, "Consolidate functional
  programming trio into functions.spl")
- every commit reachable from `HEAD` — **382 bytes**

`git merge-base --is-ancestor 289d102ba64 HEAD` answers **NO**: the only
surviving full copy sits on a lineage that is not an ancestor of `main`, so the
content cannot be recovered with a plain `git restore` from history on this
branch.

## Why not fixed now

Restoring the module means porting ~49 KB of table/cache/history code from a
divergent 2026-02 lineage onto the current stdlib API surface (the sibling
modules have since moved to `std.nogc_sync_mut.io.file_ops` /
`std.nogc_sync_mut.io.dir_ops` and `std.cli.cli_parser`, none of which the
2026-02 copy used). That is a port, not a revert, and it cannot be validated
from the CLI option surface alone — it needs the dashboard table fixtures that
were lost with it.

What *was* fixed in this pass is only the CLI entry point:
`src/app/dashboard/main.spl` now implements the shared log-mode/progress option
surface (help, JSON usage, dot progress, invalid-mode rejection,
unknown-command error), which is what
`test/02_integration/app/dashboard_log_modes_spec.spl` asserts. The data model
above is still missing.

## RECOVERY: the lost content is still in this object store (verified)

The claim above that the content "cannot be recovered with a plain `git restore`"
is true only for a *branch-relative* restore. The blob itself is present locally
and can be read directly, no lineage checkout required:

```bash
git cat-file -p 2ee3fed72cd8e6538646983b84765c4787fc175a > /tmp/dash_old.spl   # 26,786 bytes, 37 fns
```

All ten symbols this bug reports as existing nowhere are defined in that blob —
verified by symbol grep, not by size:

| symbol | defs in blob |
|---|---|
| `DASHBOARD_CACHE_PATH` | 1 |
| `DASHBOARD_TABLE_DIR` | 1 |
| `TABLE_NAMES` | 2 |
| `TABLE_HEADERS` | 2 |
| `ensure_dirs` | 2 |
| `load_table` | 8 |
| `header_index` | 8 |
| `today_date` | 1 |

Its header comment reads *"Core dashboard (CLI entry, utilities, collectors,
commands, export, serve)"* and it already imports the sibling modules that are
still on disk today (`app.dashboard.framework_policy`,
`app.dashboard.render.adapter`, `dashboard_alerts_and_queries`), so it is the
matching counterpart of the surviving files rather than an unrelated old draft.

Note the size discrepancy with the body of this report: the recoverable blob is
**26,786 bytes**, not 49,698. Whoever ports this should diff against the blob
above rather than trusting either number.

## Ownership warning — do NOT restore this unilaterally

Every commit touching this path in recent history is on the **`llm-caret`**
lane (`fix(llm-caret): localize phase3 carrier blockers`), which is active
development with a live session. The truncation may be deliberate localization
rather than an accident. This entry deliberately stops at recording the
recovery path; the decision to restore belongs to the owner of that lane.


## Verification 2026-08-17 (wave_00 w0001/app_1) — REPRODUCED, STILL OPEN

Classified by CONTENT of current source, not by SHA ancestry.

- `src/app/dashboard/collectors.spl` no longer exists; it was renamed to
  `src/app/dashboard/dashboard_collectors.spl`. The dangling import moved with
  it, so the doc's original file:line reference was stale but the DEFECT is not.
- `src/app/dashboard/dashboard_collectors.spl:8`:
  `use app.dashboard.main.{Table, load_table, load_table_named, header_index, get_field, count_eq, sum_int, count_nonempty, write_table, today_date, itos, DASHBOARD_TABLE_DIR}`
- `src/app/dashboard/main.spl` is 87 lines and defines none of them. Its own
  header comment, lines 7-8, states the gap and points at this doc:
  "The dashboard data model (tables, cache, collectors) is still missing from
  this module — see doc/08_tracking/bug/dashboard_main_lost_table_model_2026-08-04.md."
- The symbols are defined NOWHERE under `src/app/dashboard/`.
  `src/app/dashboard/dashboard_export_runtime.spl:8` imports the same missing
  set plus `DASHBOARD_CACHE_PATH`, `DASHBOARD_HISTORY_DIR`, so BOTH modules are
  dead, not just one.

Live reproduction (`nice -n 19 bin/simple run src/app/dashboard/dashboard_collectors.spl`):

```
[use-warning] 'Table' is named in `use app.dashboard.main.{...}` but module '.../src/app/dashboard/main.spl' does not provide it (imported from src/app/dashboard/dashboard_collectors.spl)
... (12 such warnings: Table, load_table, load_table_named, header_index,
     get_field, count_eq, sum_int, count_nonempty, write_table, today_date,
     itos, DASHBOARD_TABLE_DIR)
rc=0
```

**The exit code is 0.** Twelve unresolved `use` symbols degrade to warnings and
the process exits successfully — this is the silent-wrong-result class, not a
loud failure. That resolver-level fail-open is a SEPARATE and broader defect
than this row and is out of this slice's file scope; filed here as an
observation for whoever owns the `use`-resolution lane.

Not fixed here: restoring the model (Table + SDN load/write + header_index /
get_field / count_eq / sum_int / count_nonempty / today_date / itos and the
three path constants) is a feature restoration, not a patch, and was out of
budget for this lane. Status stays OPEN with the evidence above.
