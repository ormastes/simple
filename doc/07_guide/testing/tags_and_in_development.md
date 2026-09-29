# Test tags and the in-development backlog

*Companion to the test-writing guides (`doc/07_guide/ui/testing/writing_ui_tests_with_sspec.md`,
`.claude/rules/testing.md`, the `spipe` skill). Added 2026-08-23.*

## Tagging a test

A tag is a line in the file's docstring header or a comment directive:

```
"""
# my feature spec
@tag: in-development
@tag: gpu
"""
```

All of `@tag: a, b`, `# @tag: a`, `@tag:a` and `tag: "a"` are accepted — the
parser is `std.test_runner.extract_tags`, and `std.tag_query` reuses it rather
than growing a second one that could drift.

Tag names are normalised (lowercased, `_` folded to `-`), so `in_development`
and `in-development` are **one** category with one count. The canonical
spelling is the hyphenated one, matching the ~69 existing `@tag:` specs.

## `in-development`

`@tag: in-development` means: **this test is expected to FAIL.** Whole-suite
runs skip it, and the runner reports how many were skipped for that reason.
It is deliberately *not* the same as `skip` (environment-conditional) or
`pending` (not written yet) — it is written, it runs, and it is red on
purpose because the feature it pins is still being built.

It is reported as its **own category** everywhere. It is never folded into
"passed" and never dropped from the total; see "Reconciliation" below.

## `simple tags` — querying the backlog

```sh
bin/simple tags                          # every tag in use, with counts
bin/simple tags --tag in-development     # the specific items carrying one tag
bin/simple tags --root test/01_unit      # restrict the scan (repeatable)
bin/simple tags --json                   # machine-readable
```

Default roots are `test` and `src`.

### Why a top-level command and not `simple test --tag ... --list`

Two reasons, both concrete:

1. **It queries source, it does not run tests.** `simple tags` reads `@tag:`
   annotations out of files. Hanging it off `simple test` would make it look
   like a run-filter that selects which tests execute, which it is not.
2. **Runner independence.** `--tag`/`--show-tags` exist today only in the
   **Rust** runner (`src/compiler_rust/driver/src/cli/test_runner/args.rs:24`,
   `execution.rs:911,923-925`); the pure-Simple runner parses only
   `# @di_test` and `# @exec_limit` and has no `@tag:` branch at all. A
   listing built as a runner flag would therefore work on one runner and not
   the other. `simple tags` works on **both**, because it never asks a runner
   anything.

It also follows the existing dispatch convention exactly — one command name
maps to one `src/app/<name>/main.spl` in `src/app/cli/dispatch/table.spl`,
the same shape as `targets`, `linkers` and `stats`.

## Where the count shows up

| Surface | What it shows |
|---|---|
| `bin/simple stats` | `In development: <n>` under `Tests:`, plus `Other: <n> (unclassified)` when the categories do not add up |
| `bin/simple stats --json` | `test_status.{total,passed,failed,skipped,pending,in_development,unclassified}` in the `simple.stats.v2` schema |
| `doc/08_tracking/test/test_result.md` | `| In Development | <n> |` row, emitted unconditionally |
| `doc/08_tracking/feature/pending_feature.md` | `| In Development | <n> | Expected-fail, skipped by suite runs |` |
| `bin/simple tags` | the count **and** the list |

The row in `test_result.md` is emitted even when it is zero. A category that
disappears when empty is a category nobody notices when it stops being empty.

### A trap worth knowing about

`src/app/stats/dynamic.spl` contains a second, older JSON emitter
(`format_json`, ~line 708). It is **unreachable**: `run_stats` returns at the
`is_json` branch (~line 371) after printing the v2 projection, so nothing
below it ever runs on the `--json` path. Adding a field there looks correct,
compiles, and does nothing. The live emitter is `app.stats.json_v2`, and the
counts it prints come from `app.stats.test_status` — the same single reader
the text output uses, so the two cannot disagree.

## Reconciliation

`passed + failed + skipped + pending + in-development + other == total`.

This is enforced, not merely hoped for:

```sh
sh scripts/check/check-test-summary-reconciles.shs
```

`PASS`/`FAIL`/`ERROR` as the last line of stdout, exit 0/1/2; a run that read
no metrics is ERROR, never a pass. Its selftest is fatal (4 fixtures).

**It is currently ADVISORY because it is honestly RED:** `test_result.md`
reads Total 770 / Passed 0 / Failed 0, and `test_db.sdn` has a broken
file→name join. Filed as
`doc/08_tracking/bug/test_db_incoherent_totals_and_broken_file_name_join_2026-08-23.md`.
Until that is fixed, **the DB-sourced counts are only as trustworthy as the
DB, which is currently not trustworthy**; the `simple tags` counts are read
from source annotations and are independent of it.
