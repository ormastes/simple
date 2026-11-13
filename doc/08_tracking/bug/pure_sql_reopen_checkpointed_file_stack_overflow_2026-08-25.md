# Pure-Simple SQL: re-opening an already-checkpointed file stack-overflows — 2026-08-25

Status: OPEN. Tier: EMBEDDED (`std.database.pure_sql`,
`src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/pure_database.spl`).
Found while fixing
`llm_caret_pure_sql_where_text_pk_returns_no_rows_2026-08-25.md`; a different
defect, not fixed there.

## Reproduce

Script: `PureDatabase.open_deferred(path)` -> `CREATE TABLE IF NOT EXISTS mm
(id TEXT PRIMARY KEY, value TEXT NOT NULL)` -> INSERT one row ->
`checkpoint()`. First run on a fresh path: fine. Second run of the same script
on the SAME path (file now holds the checkpointed content):

```
thread 'simple-main' (670999) has overflowed its stack
fatal runtime error: stack overflow, aborting
```

Binary: `bin/release/x86_64-unknown-linux-gnu/simple 60650360 2026-08-23
04:47:05 +0000` (Rust seed). The affected llm_caret specs dodge it only
because they `file_delete` the path first. Suspect: the `_load_from_disk` /
restore path (~`:1061`, `:1640`); not bisected yet.

## Unblock condition

Opening an existing checkpointed file must load it (or return `Err`), never
abort. Ship the fix with a reproduce case next to
`test/01_unit/lib/database/pure_sql_select_cache_spec.spl`.

## Narrowing (2026-08-25, post cache-fix)

Re-verified after the SELECT-cache fix landed locally: still aborts, rc=134,
2/2 runs on the same `t.db` (`/mnt/data/tmp/claude-1000/sql_reopen_{1,2}.log`),
so it is independent of that defect. **The minimal sequence in "Reproduce" is
NOT sufficient on its own**: `pure_sql_select_cache_spec.spl`'s deferred-file
case does `open_deferred` -> `CREATE TABLE IF NOT EXISTS mm (id TEXT PRIMARY
KEY, value TEXT, n INTEGER)` -> DELETE -> INSERT -> `checkpoint()` on the fixed
path `/tmp/pure_sql_select_cache_spec.db` and reopened that checkpointed file
cleanly on runs 2 and 3. The two schemas differ in `value TEXT NOT NULL`
(overflowing) vs `value TEXT` (fine) and in `CREATE TABLE` vs `CREATE TABLE IF
NOT EXISTS` on an existing table. Start the bisect there — the persisted
column-constraint text is the leading suspect for a recursion in the
reload/parse path. Reproducer script:
`/mnt/data/tmp/claude-1000/sqlrepro/repro.spl` (run twice on the same path).

---

## Addendum 2026-11-13 — lane live-p3-l4 (work/live-p3-l4-20261113, base f790f7f266e) — FIXED (.spl, engine-independent)

**Re-verified on the current Windows seed (bin/simple.exe, build-commit
0791c2b7f4a7 refresh #8184): no stack overflow, but reopen still failed** —
`PureDatabase.open` on the checkpointed `value TEXT NOT NULL` file returned
`ConnectionFailed: truncated or corrupt pure database payload` under the
default (JIT-preferred) `run` lane. The interpreter lane (`--mode=interpreter`)
passed the identical sequence.

**Root cause isolated by in-process instrumentation** (temporary `print` at
the v3 envelope validation, since removed): the intact on-disk image
(content 173 B, payload 87 B) failed only the `declared_length` operand —
`_pdb_v2_decimal_length("87")` returned `Some(3)` inside the loader while a
manual replication of the same algorithm returned `Some(87)`.

**Underlying defect is in the SEED JIT, not this library.** Measured
differentially on the same binary:

| lane | `"87".parse_int()` | `"abc".parse_int()` | `int("87")` | `"1.5".parse_float()` |
|---|---|---|---|---|
| `SIMPLE_EXECUTION_MODE=interpret` | `Some(87)` | `None` | `87` | `Some(1.5)` |
| `SIMPLE_EXECUTION_MODE=jit` (and default `run`) | **`Some(nil)`** | `None` | `87` | **`Some(nil)`** |

The JIT lowers `parse_int`/`parse_i32`/`parse_i64` to `rt_string_parse_int`
(codegen/instr/calls.rs:4579 — a TAGGED value, NIL on failure) and
`parse_float` likewise to `rt_string_to_float`, but the tagged→`Option`
boxing on the success path stores nil. Every JIT-compiled consumer of the
Option-returning parse family sees `Some(nil)` for valid input.
`text.to_int()`/`text.to_f64()` are JIT-correct (measured: `87` / `1.5`).
This is a distinct, unrecorded seed codegen defect (the FIXED
`seed_jit_conversion_call_text_parse_2026-11-06.md` covers only the
conversion-call `T(x)` form). Seed lane: fix the JIT Option-boxing of
tagged-returning externs; until then the interpreter is the only correct
engine for these methods.

**Fix landed here (bounded, engine-independent):**
`src/lib/nogc_sync_mut/database/pure_sql/_PureDatabase/row_value_helpers.spl`
- new `_pdb_decimal_parse_strict(value) -> i32?`: manual digit accumulation
  over `char_code_at` only (all total ops with identical interpreter/JIT
  behavior); accepts exactly the persisted `to_text` spellings of an i32
  (optional `-`, 1..=10 digits, `[-2147483648, 2147483647]`, no leading
  zeros).
- `_pdb_v2_decimal_length` now delegates to it (no `parse_int`).
- `_deserialize_row_v2` canonicality: kind `I` uses the strict parser; kind
  `R` uses `payload.to_f64().to_text() != payload` instead of
  `parse_f64`+unwrap (same accept/reject outcome, JIT-safe).

**Verification (this lane, before/after, same binary):**
- Repro probe (`open_deferred` → `CREATE TABLE IF NOT EXISTS mm (id TEXT
  PRIMARY KEY, value TEXT NOT NULL)` → INSERT → `checkpoint()` → second
  `open_deferred` same path): before = `RUN2 ERR: truncated or corrupt pure
  database payload` (default lane); after = `RUN2 OK rows=1` under BOTH the
  default JIT-preferred lane and `SIMPLE_EXECUTION_MODE=interpret`.
- Regression spec added next to the cache spec per this record's unblock
  condition: `test/01_unit/lib/database/pure_sql_reopen_checkpointed_spec.spl`
  — 1/1 PASS under both engines.
- `test/01_unit/lib/database/pure_sql_select_cache_spec.spl` — 10/10 PASS
  (was 10/10 before; unchanged).
- `pure_sql_autoincrement_spec.spl` — 2/2 PASS.
- `pure_sql_query_debug_v1_spec.spl` — ERROR 0 executed, verified
  byte-identical verdict with the fix stashed (pre-existing, unrelated).

The original Linux-seed stack-overflow manifestation (rc=134) was not
re-observed here; if it recurs on a rebuilt seed, re-open with the
reproducer spec above.
