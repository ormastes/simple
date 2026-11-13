# bug-resolve calls three BugDatabase methods that do not exist

Status: confirmed genuine product bug (runtime `EX_SOFTWARE` crash, exit 70).
Every non-`--help` `bug-resolve` invocation aborts in the seed runtime.

## Evidence

Repro (Windows host, seed binary, fixture bug DB under a temp dir):

```
simple run src/app/bug_resolve/main.spl \
  --id=repro_bug --date=2026-05-24 \
  --input-tokens=-1 --output-tokens=-1 --cache-read-tokens=-1 --cache-create-tokens=-1 \
  --token-provider=test-provider --token-source=test-session --knowledge=none --log-mode=json
```

stderr ends with:

```
Runtime error: Function 'BugDatabase.token_category_for_bug' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not a
program error. Refusing to substitute a placeholder value ...
```

exit code 70 (`EX_SOFTWARE`).

`src/app/bug_resolve/main.spl:152-153,175` calls three methods on the
`BugDatabase` value returned by `load_bug_database`:

- `db.token_category_for_bug(id)` (line 152)
- `db.comparable_token_average(token_category, id)` (line 153)
- `db.add_token_usage(...)` (line 175)

`grep -c` over both `src/lib/nogc_sync_mut/database/bug.spl` and
`src/lib/nogc_async_mut/database/bug.spl` shows **zero** definitions of
`add_token_usage`, and the `BugDatabase` method set is only
`add_bug`, `add_investigation_log`, `update_bug`, `resolve_bug`, `save`,
`append_open_bugs_preserving_legacy`, `save_exclusive`. `token_category_for_bug`
and `comparable_token_average` are referenced nowhere else in the tree.

## Cause and scope

`bug_resolve` was written against a token-accounting API on `BugDatabase`
(`bug_token_usage` cohort category, comparable average, structured usage rows)
that was never implemented (or was removed) from `std.database.bug`. The app
compiles because the methods are only resolved dynamically; the seed runtime
then hits an unresolved-symbol dispatch gap and hard-aborts with exit 70, so
`bug-add` works but every real `bug-resolve` operation crashes.

## Correctness gate for a repair

1. Implement `token_category_for_bug`, `comparable_token_average`, and
   `add_token_usage` on `BugDatabase` against the `bug_token_usage` SDN table
   (the fixture schema already declares that table), or change `bug_resolve` to
   stop requiring them.
2. Decide the intended resolve semantics: the knowledge-link gate ("above 2x
   comparable average", "partial token usage cannot be compared") depends on
   the average computation; pin it with a unit test on `BugDatabase` before
   wiring the CLI back up.
3. Re-run `test/02_integration/app/bug_add_resolve_log_modes_spec.spl` and the
   fixture repro above; all four currently-red scenarios
   (json resolve, knowledge gate, partial receipt, invalid tokens) must pass.
