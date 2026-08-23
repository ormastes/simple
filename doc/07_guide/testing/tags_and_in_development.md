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
| `bin/simple stats` | `Passed` / `Failed` / `In development` always, even at zero and even with no recorded run; `unexpected pass` and `BROKEN` when non-zero; `Skipped (host-unavailable)` as its own separate count; `Other: <n> (unclassified)` when the categories do not add up |
| `bin/simple stats --json` | `test_status.{total,passed,failed,skipped,pending,in_development,in_development_unexpected,in_development_broken,unclassified}` in the `simple.stats.v2` schema — every field always emitted |
| `doc/08_tracking/test/test_result.md` | `| In Development | <n> |` row, emitted unconditionally |
| `doc/08_tracking/feature/pending_feature.md` | `| In Development | <n> | Expected-fail, skipped by suite runs |` |
| `bin/simple tags` | the count (always, even at zero) **and** the list, labelled source-derived |

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

`passed + failed + skipped + pending + in-development + unexpected-pass + other == total`.

`BROKEN` is **not** an addend: it already counts inside `failed`, because it
fails the run. Adding it again would manufacture a phantom remainder.

This is enforced, not merely hoped for:

```sh
sh scripts/check/check-test-summary-reconciles.shs
```

`PASS`/`FAIL`/`ERROR` as the last line of stdout, exit 0/1/2; a run that read
no metrics is ERROR, never a pass. Its selftest is fatal (4 fixtures).

**It is currently ADVISORY because it is honestly RED:** `test_result.md`
reads Total 770 / Passed 0 / Failed 0, and `test_db.sdn` has a broken
file→name join. Filed as
`doc/08_tracking/bug/test_db_incoherent_totals_and_broken_file_name_join_2026-08-23.md`,
and other lanes have since found two further reasons the numbers lie: a
post-run `runtime_file_rename` error forcing rc=1 on passing runs, and a
`@cover` preflight gate that manufactures hundreds of phantom failures with a
fully-formed `Results:` line and **zero specs executed**.

So, plainly:

| count | source | trustworthy today |
|---|---|---|
| `bin/simple tags` | `@tag:` annotations in source | **yes** |
| `stats`, `test_result.md`, `stats --json` | the test DB | **no** — see the records above |

### A pre-fix pass rate is an OVERCOUNT, not just a gap

Until `TestStatus.InDevelopment` existed, the DB write site picked a row's
status with `if file_result.is_ok()`. A neutralised in-development file has
`failed == 0`, so `is_ok()` was **true** and the row was written as
**`passed`**.

So a DB written before that fix does not merely omit in-development — it
**counts those specs as passing**. Every `Passed` figure and every
`pass_rate` from such a run is inflated by the in-development population,
and the totals still reconcile perfectly, so nothing in the report looks
wrong. Treat any historical pass rate accordingly.

These surfaces query both `in_development` and `in-development`, so they
begin reporting correctly as soon as a run is recorded by a runner carrying
the new status — no further change here.

**The reconciliation gate cannot catch this class.** Folding in-development
into `passed` moves a count from one addend to another; the sum is
unchanged, so `check-test-summary-reconciles.shs` stays green throughout.
A passing reconciliation is evidence that no category was *dropped*. It is
**not** evidence that every category was *classified correctly*, and the two
are easy to confuse. This is pinned by an example in
`in_development_tag_reporting_spec.spl` that asserts the folded numbers
still reconcile — the first draft of that example asserted the opposite and
failed, which is how the limit was found.

### Adding a new status? Read this first

`str_to_status` (`test_db_types.spl:132`) ends in
`case _: TestStatus.Skipped`. An unrecognised status string is **silently
relabelled a skip** — no error, no warning, and the result looks like a
legitimately-skipped test. Both in-development spellings are explicit cases
so they cannot hit it, but any *new* status added without touching that
function will be silently mislabelled.

## Dev ids — running exactly your own in-development set

`# @tag:in-development` says a spec is work-in-progress. It does not say
*whose*. With several lanes tagging at once, `--tag in-development` returns
everybody's WIP. A **dev id** names one workstream:

```
# @tag: in-development, dev-id-auth-rework
```

The id is whatever follows the reserved `dev-id-` prefix. It is an ordinary
`@tag:` name — no new grammar, no new parser, and visible to every tag
consumer (including the Rust runner's `--tag`) the moment you write it.

### What a dev session types

```sh
bin/simple tags --dev-ids                                      # ids + counts
bin/simple tags --dev-id auth-rework                           # the specs
bin/simple test $(bin/simple tags --dev-id auth-rework --paths)   # run just those
bin/simple test $(bin/simple tags --in-development --paths)       # run all WIP
bin/simple test $(bin/simple tags --no-in-development --paths)    # run WIP-free
```

`--paths` prints bare newline-separated paths so the selection composes with
`$( )`. That is deliberate: it works identically on both engines, whereas a
filter flag living in one runner only would be a trap.

### Default is include

| flag | executes |
|---|---|
| *(none)* | everything — in-development **included** |
| `--in-development` | only in-development specs |
| `--in-development=<id>` | only that workstream |
| `--no-in-development` | everything except in-development specs |

Including by default is the landed rule, not a new one: a tagged spec always
executed, and it is only its **verdict** that a sweep neutralises. Selection
changes what runs; it never changes how a verdict counts. `--no-in-development`
is the only mode that stops a tagged spec running, and it is opt-in, so
nothing silently loses the `IN-DEVELOPMENT UNEXPECTED PASS … ready to promote`
signal that running them exists to produce.

`--dev-ids` also prints an **Unnamed** category: in-development specs with no
dev id. Those are reachable by no id-scoped run, so they are shown rather than
hidden. A `dev-id-` tag on a spec that is no longer in-development is not
counted, so promoting a spec removes it from its workstream automatically.

Design record, including the four rejected syntaxes:
`doc/05_design/app/testing/in_development_dev_ids.md`.
