# Feature expert: bug-resolve completion token receipts

## What it does
`src/app/bug_resolve/main.spl` closes a bug and records a completion token receipt.
Required flags: `--id --date --input-tokens --output-tokens --cache-read-tokens
--cache-create-tokens --token-provider --token-source --knowledge` (use `unavailable`
and `none` explicitly).

## Data model (`src/lib/nogc_sync_mut/database/bug.spl`)
- `BugTokenCategory` enum, from the bug's file path prefix (compiler, runtime, library,
  application, os, test, other).
- `BugTokenReading` = `Unavailable | Count(BugTokenCount)`; `bug_token_total` sums them
  (Unavailable if any is; `Err` on i64 overflow).
- `BugDatabase.token_category_for_bug(id) -> BugTokenCategory?`
- `BugDatabase.comparable_token_average(category, exclude_id) -> Result<BugTokenReading, text>`:
  mean total over other Closed bugs in the cohort.
- `BugDatabase.add_token_usage(id, BugTokenUsage) -> bool`: appends a `bug_token_usage` row;
  rejects unknown ids, unsafe fields, and partial readings without a knowledge link.
  Call `save()` afterwards.

## Gates in the CLI
Total above 2x the cohort average, or a partial (some-unavailable) receipt, requires an
existing repository `--knowledge` path. Nothing is written before every check passes
(writes happen in memory, `save()` is last).

## Pitfalls
- Seed: tail-position `match x.parse_i64(): case Some(v): Struct(value: v)` aliases the
  struct across calls; parse into a `val` first.
- Fixtures: do not hand-write `bug_db.sdn` (no seal sidecar); let `bug-add` create it.
- Tests: `test/01_unit/app/bug_resolve/bug_resolve_cli_spec.spl`.
