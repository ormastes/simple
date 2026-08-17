# Seed interpreter SQLite emulation ignores WHERE on DELETE (silent full truncate)

Found: 2026-08-17, lane `.spipe/simple_enterprise_suite` W12-B, while bounding
the enterprise request throttle's counter table.

Status: RESOLVED 2026-08-17 — see the note at the bottom.

## What happens

In INTERPRETER mode the Rust seed emulates SQLite in
`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`. Its statement
dispatcher contains:

```rust
if lower.starts_with("delete from ") {
    let table_name = sql["DELETE FROM ".len()..].split_whitespace().next().unwrap_or("");
    if let Some(table) = conn.db.tables.get_mut(table_name) {
        conn.changes = table.rows.len() as i64;
        table.rows.clear();
        table.next_id = 1;
        return 1;
    }
```

The WHERE clause is never parsed and never evaluated. **Every** `DELETE FROM t
...` clears the whole table and reports success.

## Measured

Rust seed `bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes,
2026-08-16), interpreter mode, via `sqlite_open` / `sqlite_execute`:

| statement | rows before | rows after | expected after |
|---|---|---|---|
| `DELETE FROM t WHERE 1=0` | 2 | **0** | 2 |
| `DELETE FROM t WHERE CAST(w AS INTEGER) < 1` (w in {'0','1'}) | 2 | **0** | 1 |

Both returned `true`. A caller cannot distinguish "deleted the rows I asked
for" from "deleted everything".

## Why it matters beyond this lane

The C runtime (`src/runtime/runtime_sqlite.c`) hands the statement to real
libsqlite3, which honours WHERE. So one source statement means two different
programs depending on execution mode, and the difference is silent data loss
in the mode used for every spec run. Any module that adopts a conditional
delete will pass its specs while destroying rows it meant to keep.

## Fix

Parse and evaluate the WHERE clause in the emulation, or — if that is out of
scope for the emulation's fidelity goals — make an unparsed WHERE an ERROR
(`sqlite_set_error`) rather than a success. Failing closed is acceptable;
silently widening a delete is not.

## Workaround in place

`src/lib/nogc_sync_mut/enterprise_store/store.spl` exposes only
`store_truncate(store, table)` — the unconditional delete both backends agree
on. `src/lib/nogc_sync_mut/enterprise_session/throttle.spl` establishes the
predicate ("every retained row belongs to an elapsed window") in pure Simple
first, so the unconditional delete is provably equal to the conditional one at
the moment it runs. No conditional DELETE exists anywhere in the enterprise
suite.

## RESOLVED 2026-08-17

Fixed in `src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs`
(`sqlite_execute_statement` DELETE branch):

- `DELETE FROM t` with no WHERE keeps its full-truncate behaviour.
- `DELETE FROM t WHERE lhs = rhs` (single equality; operands may be a column
  name or a literal, numeric or quoted text) now deletes only matching rows
  and sets `conn.changes` to the actual deleted count. `WHERE 1=0` deletes
  nothing.
- Any other WHERE clause (AND/OR/NOT, comparisons, LIKE, IN, CAST/parens)
  **fails closed**: `sqlite_set_error("unsupported DELETE WHERE clause
  (emulation): ...")` and returns 0 — never a silent widened delete.

Verified with `cargo check --release --bin simple` (clean) — the running
`bin/simple` seed predates this fix until the next full bootstrap redeploys it.
