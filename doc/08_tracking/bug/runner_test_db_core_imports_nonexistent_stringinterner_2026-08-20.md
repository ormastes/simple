# `RunnerTestDbCore` cannot be constructed — `test_db_core.spl` imports a `StringInterner` that does not exist

- **Filed:** 2026-08-20
- **Status:** OPEN — root-caused, one-line-ish fix identified, not applied
- **Severity:** medium (the module is unusable and untestable; it is NOT on the
  live `bin/simple test` path, so nothing is currently broken *because* of it)
- **Found while:** investigating
  `doc/08_tracking/bug/test_runner_spins_at_100pct_after_summary_2026-08-18.md`

## MEASURED

`src/lib/nogc_sync_mut/test_runner/test_db_core.spl:9` declares:

```
use std.test_runner.string_interner.StringInterner
```

`src/lib/nogc_sync_mut/test_runner/string_interner.spl` defines **no such
symbol**. The struct it actually defines is `TestDbStringInterner` (`:7`), with
`static fn empty() -> TestDbStringInterner` at `:12`. The comment at `:34-35`
records why: the class *was* called `StringInterner` and was deliberately renamed
because three same-named classes were being co-loaded and dispatching by name.
The rename was not propagated to this importer.

`RunnerTestDbCore.empty()` (`test_db_core.spl:38`) calls `StringInterner.empty()`
in its initialiser. Because the name resolves to nothing, it evaluates as an
empty dict and the call dies:

```
error: semantic: method `empty` not found on type `dict` (receiver value: {})
```

Reproduce (any of `bin/simple run`, `SIMPLE_EXECUTION_MODE=interpreter
bin/simple run`, or a spec under `bin/simple test` — all three produce the
identical error):

```
use std.nogc_sync_mut.test_runner.test_db_core.{RunnerTestDbCore}
fn main():
    var db = RunnerTestDbCore.empty()
    print "tests={db.tests.len()}"
```

A narrower probe confirms the missing symbol directly, rather than inferring it:

```
use std.nogc_sync_mut.test_runner.string_interner.{StringInterner}
```
->
```
[use-warning] 'StringInterner' is named in `use ...string_interner.{...}` but
module '.../nogc_sync_mut/test_runner/string_interner.spl' does not provide it
error: semantic: variable `StringInterner` not found
```

### Pre-existing, not introduced by concurrent work

Verified by A/B in one tree with one binary: the failure reproduces identically
on the **stashed, unmodified** `test_db_core.spl` (`git checkout --` then re-run)
as on the working-copy version. Binary:
`bin/release/x86_64-unknown-linux-gnu/simple` (the Rust seed;
`readlink -f bin/simple`).

Note the import is a **warning**, not an error, at import time — the failure is
deferred to the call site and surfaces as a confusing `type dict` message. That
is why this sat unnoticed.

## Why it did not break the test runner

`test_db_core` is **not** on the live `bin/simple test` path.
`test_runner_helpers.spl:229` `update_test_database` holds a `RunnerTestDb` from
`std.test_runner.test_db_compat`, which wraps `std.database.test_extended`
(`src/lib/nogc_sync_mut/database/test_extended/`). `test_db_compat.spl` imports
only `parse_rfc3339_to_micros` from `test_db_core` — a free function that never
touches the broken class. So the module is loaded, but the dead class is never
constructed.

Consequence for testing: `RunnerTestDbCore` has **no reachable construction
path**, so none of its behaviour can be covered by a spec. A reproduce spec
written against it during the spin investigation had to be withdrawn rather than
landed red, because it would have failed on this import defect and not on the
behaviour under test.

## Fix

Rename the import and the two use sites to the real symbol:

- `test_db_core.spl:9` — `use std.test_runner.string_interner.TestDbStringInterner`
- `test_db_core.spl:21` — field `interner: TestDbStringInterner`
- `test_db_core.spl:40` — `interner: TestDbStringInterner.empty()`

**Do not fix it by re-adding a `StringInterner` alias** to
`string_interner.spl`: that name was removed on purpose (see the `:34-35`
comment and `database.spl:102-106`, which records shared names on
`StringInterner` dispatching across co-loaded same-name classes and aborting
test-result persistence right after the summary). Re-introducing the name would
reopen that defect.

## Verification bar for the fix

1. The probe above prints `tests=0` instead of erroring.
2. A spec constructing `RunnerTestDbCore.empty()` and driving
   `update_test_result` runs green — this is the coverage the module has never
   had.
3. Confirm no `StringInterner` symbol is reintroduced:
   `/usr/bin/grep -rn 'StringInterner' src/lib/nogc_sync_mut/test_runner/` should
   show only `TestDbStringInterner`.

## Related

- `doc/08_tracking/bug/test_runner_spins_at_100pct_after_summary_2026-08-18.md`
  — the investigation this was found during; §4 of its 2026-08-20 note records
  the same evidence in less detail.
