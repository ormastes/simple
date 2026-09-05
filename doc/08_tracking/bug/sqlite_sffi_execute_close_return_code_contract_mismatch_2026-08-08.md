# sqlite_sffi return-code checks match the Rust seed but are inverted for the native C runtime

- **Date:** 2026-08-08
- **Severity:** High (silent, total failure of write reporting under the native runtime)
- **Status:** OPEN — identified, not fixed
- **Area:** `src/lib/nogc_sync_mut/io/sqlite_sffi.spl`, `src/runtime/runtime_sqlite.c`

## Summary

There are two implementations of the `rt_sqlite_*` primitives, and they use
**opposite success conventions**. `sqlite_sffi.spl` checks for only one of them.

| primitive | native C runtime | Rust bootstrap seed | `.spl` check |
|-----------|------------------|---------------------|--------------|
| `rt_sqlite_execute` | `rc == SQLITE_OK ? 0 : -1` (`src/runtime/runtime_sqlite.c:93`) | returns `1` on success (`sffi_db.rs:1175`, and `rt_sqlite_execute_batch_fn` at `sffi_db.rs:1188` tests `!= 1`) | `result == 1` (`sqlite_sffi.spl:148`) |
| `rt_sqlite_execute_batch` | delegates to `rt_sqlite_execute` (`runtime_sqlite.c:96`) | returns `1` on success | `result == 1` (`sqlite_sffi.spl:170`) |
| `rt_sqlite_close` | `rc == SQLITE_OK ? 0 : 1` (`runtime_sqlite.c:82`) | returns `1` on success (`sffi_db.rs:1161`) | `result == 1` (`sqlite_sffi.spl:126`) |

Under the **native C runtime**:

- `sqlite_execute` and `sqlite_execute_batch` return `true` only when the
  runtime returns `1`, which it never does. Success (`0`) and error (`-1`) both
  map to `false`. Every `CREATE`/`INSERT`/`UPDATE`/`DELETE` executed through
  this path **is applied to the database but reported to the caller as a
  failure**.
- `sqlite_close` is inverted the other way: the C runtime returns `0` on
  success and `1` on failure, so `result == 1` reports success **only when the
  close actually failed**.

This propagates directly into the typed database layer:
`Database.exec` (`src/lib/nogc_sync_mut/database/sql/connection.spl:85-88`)
turns the false into `Err(DbError.QueryFailed)`, as do `Transaction.execute`
and the whole savepoint family. A caller doing the right thing — checking the
`Result` — concludes the write failed while the data was in fact committed.

The native-project test fixture already encodes the C convention explicitly:
`src/compiler_rust/compiler/src/pipeline/native_project/tests.rs:2898-2907`
asserts `rt_sqlite_execute(...) == rt_value_int(0)` for success and
`== rt_value_int(-1)` for `"invalid sql"`. So the C side is intentional and the
`.spl` side simply never matched it.

## Why this is filed rather than fixed

Any single-sided change breaks the other engine: the seed returns `1` for the
same success for which C returns `0`, and the seed returns `0` for the error
case for which C returns `-1`. A naive `result == 0 or result == 1` would make
seed-side errors read as success. The correct fix is to settle one convention
across both implementations (and `rt_sqlite_close` needs to be brought in line
too, in the opposite direction from `execute`) — that is a cross-cutting
contract audit of the whole `rt_sqlite_*` surface, not a one-line change.

Neither side is verifiable from the currently available path: `bin/simple` is
the Rust bootstrap seed, so `bin/simple test` exercises only the seed
convention, where `result == 1` happens to be correct. That is precisely why
this has stayed invisible.

## Unblock condition

Enumerate every `rt_sqlite_*` primitive, tabulate the return convention on both
the C runtime and the seed, pick one, and change the other side plus
`sqlite_sffi.spl` together. Verify the native side with a native-path spec, not
the interpreter.

## Discovered by

Fallout from investigating
`sql_savepoint_name_multistatement_injection_2026-08-08.md`. A probe showed
`db.exec("INSERT INTO victim VALUES (1)", [])` returning `is_err = true` on the
seed while `CREATE TABLE` returned `is_err = false`; chasing that difference
surfaced the two-implementation split above. (The seed-side `INSERT` failure
itself is a separate, narrower gap: the seed's in-process SQL engine does not
accept an `INSERT` without a column list.)
