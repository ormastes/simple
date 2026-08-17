# Interpreter rt_sqlite_* externs are a non-ACID SQL emulation (transactions no-op, constraints unenforced)

- Date: 2026-08-14
- Area: runtime / interpreter externs / database
- Severity: high (blocks honest durability evidence for any interpreter-mode
  spec built on `std.nogc_sync_mut.io.sqlite_sffi`)
- Found by: `.spipe/simple_enterprise_suite` Wave B probe
  (enterprise durable-store lane)

## RESOLVED 2026-08-17 (emulation-side fix): transactions + UNIQUE now enforced in the emulation

`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs` now implements
the "at minimum" path from the Suggested fix:

- `rt_sqlite_begin/commit/rollback` take the connection handle and do real
  snapshot semantics: BEGIN clones the in-memory `SqlDatabase` into
  `SqlConn.tx_snapshot`; ROLLBACK restores it; COMMIT drops it. Nested BEGIN,
  and COMMIT/ROLLBACK with no active transaction, set an error and return 0.
  SQL-text `BEGIN`/`COMMIT`/`END`/`ROLLBACK` via `sqlite_execute` route to the
  same helpers (previously they hit "unsupported SQL").
- CREATE TABLE now records per-column `UNIQUE`/`PRIMARY KEY` constraints, and
  INSERT rejects duplicates with `UNIQUE constraint failed: table.col`
  (NULLs exempt, as in SQLite).
- Companion fix: DELETE now honours a single-equality WHERE and fails closed
  on anything more complex (see
  `seed_sqlite_emulation_ignores_delete_where_2026-08-17.md`).

Verified with `cargo check --release --bin simple` (clean). The re-verification
probe (`after_rollback` empty, `dup_insert_ok=false`) becomes runnable in
interpreter mode once a rebuilt seed is deployed — the concurrently running
bootstrap owns that. Still out of scope for the emulation: FK/CHECK
constraints and PRAGMAs (unchanged), and the `int()`-over-rt_string and
`store_backend_acid` follow-ups below.

## Status 2026-08-17 (lane W10-C): PARTIALLY RESOLVED — a real ACID path now exists

`sh scripts/check/check-sqlite-backend-acid.shs` prints
`ACID — rollback removed the row, UNIQUE violation rejected` (exit 0). An AOT
`bin/simple compile <src> --native -o <bin>` binary now links real libsqlite3.

The interpreter/JIT emulation described below is **unchanged and still
non-ACID** — this bug stays OPEN for that. What changed is that the AOT path is
no longer blocked, so honest ACID evidence is obtainable for the first time.

Two defects were fixed to get there:

1. **Single-file `--native` never linked sqlite** (the blocker W9-B predicted).
   `codegen: undefined symbol: rt_sqlite_open`. Fixed in the **Rust seed** —
   unavoidable, since `bin/simple` is the seed and the pure-Simple linker that
   already lists `-lsqlite3` is not on this path:
   - `compiler/src/linker/native_binary/linker.rs`: new `object_requires_sqlite`
     (UNDEFINED-symbol test mirroring `is_sqlite_runtime_symbol`); when it
     fires, `run_link_pass` adds an on-demand `runtime_sqlite.o` and `-lsqlite3`.
   - `compiler/src/pipeline/native_project/tools.rs`: new
     `build_sqlite_runtime_object`, compiling that one TU with flags identical
     to `build_c_runtime_library`'s.
   Binaries that do not reference sqlite are untouched.

2. **`src/runtime/runtime_sqlite.c` had never once been compiled into a linked
   binary, and its integer ABI was wrong.** It tagged every integer (`v << 3`)
   and returned `SPECIAL_TRUE`/`SPECIAL_FALSE` (11/19), while
   `sqlite_sffi.spl` declares `extern fn ... -> i64` and native codegen passes
   scalars RAW. Observed: `rt_sqlite_column_count` returning 1 read as **8**,
   `rt_sqlite_query_next` read as **11**, so `while has_row == 1` never entered
   and **every query returned zero rows**. `from_int`/`as_int` are now
   identities; `query_next` returns 1/0. Strings/pointers keep their tagging
   and were always correct.

### Still open, newly identified: `sqlite_count` mis-parses via `int()`

`sqlite_count` does `int(count_str)` on a runtime-produced string and receives
the **ASCII code of the first digit** — empty table -> 48, one row -> 49.
`int("142")` on a *literal* correctly yields 142, so the defect is in `int()`
over an `rt_string`, not in sqlite. **This retires an earlier misreading in this
file and in the enterprise_store guide:** W9-B's `start_count=48` was
interpreted as "a global emulation counter"; it was ASCII `'0'`. The ACID probe
now reads presence as TEXT via `sqlite_query_value`, whose path is sound.

### Guard against vacuous evidence

The atomicity assertions W9-B deliberately withheld are now in
`test/fixture/enterprise_store/sqlite_acid_probe.spl`, gated by a non-vacuity
precondition: the probe must first show `in_tx_row1=[alpha]` and
`committed_row2=[beta]`, else the script reports `BLOCKED — probe is vacuous`.
Discrimination confirmed by running the identical probe under the interpreter
(`after_rollback_row1=[alpha]`, `dup_insert_ok=true` -> NONACID) and by
cross-reading the resulting db file with CPython's `sqlite3`.

### Remaining frontier

1. `bin/simple test` runs in the interpreter, so the enterprise specs still
   see `store_backend_acid == false` (all three remain green: 10/10, 5/5,
   10/10). Real SQLite is reachable only via an AOT `--native` binary today.
2. `store_backend_acid` is false **even natively**, and this is a layer above
   sqlite. In an AOT `--native` binary every primitive `probe_backend_acid`
   uses is correct: `store_count_text` before=`[0]`, `sqlite_begin` true,
   `store_insert2` true, mid=`[1]`, `sqlite_rollback` true, after=`[0]` — i.e.
   `before == after` is true when run standalone. Yet `store_open()` reports
   `acid=false` with `is_file=false` (a genuine sqlite connection, not the
   file-backend fallback). Suspect the state `store_open` sets up right before
   the probe (WAL pragma, CREATE TABLE batch, `marker_present` /
   `store_insert2` marker write possibly leaving a statement unfinalized).
   Next step: instrument the three values inside `probe_backend_acid`
   (`store.spl:135-143`) under `--native` and diff against the known-good
   standalone sequence.

## Symptom

Probe (`bin/release/aarch64-apple-darwin/simple run` on an in-memory db):

```
begin=true ins2=true rollback=true count_after_rollback=2   # rollback did NOT undo the insert
dup_insert=true err=                                        # UNIQUE violation reported as SUCCESS
fk_default=                                                 # PRAGMA returns nothing
```

## Root cause

The interpreter does not bind the real SQLite runtime
(`src/runtime/runtime_sqlite.c` / rusqlite). Instead
`src/compiler_rust/compiler/src/interpreter_extern/sffi_db.rs` implements a
hand-rolled SQL emulation (`sqlite_parse_create`, `sqlite_parse_insert`,
`sqlite_like`, serialize-to-file), and:

- `rt_sqlite_begin_fn` / `rt_sqlite_commit_fn` / `rt_sqlite_rollback_fn`
  ignore their arguments and return `Ok(Int(1))` — transactions are no-ops
  (sffi_db.rs:1445-1455).
- Column constraints (UNIQUE, FOREIGN KEY, CHECK) are not parsed or
  enforced; a violating INSERT succeeds.
- PRAGMA statements return nothing.

Native builds link the real SQLite, so behavior diverges interpreter-vs-native
(a differential-correctness hazard on top of the honesty hazard).

## Impact

- Any interpreter-mode spec that asserts commit/rollback atomicity,
  idempotency-key uniqueness via UNIQUE constraints, or FK integrity will
  false-green (success returns) while proving nothing.
- The enterprise durable-store lane (AC-5/AC-6 of
  `.spipe/simple_enterprise_suite/state.md`) must classify ACID evidence as
  `environment-blocked` under the interpreter and gate real evidence on a
  native-mode run with the real SQLite runtime.

## Suggested fix

Bind the interpreter externs to the real bundled SQLite (rusqlite is already
a seed dependency for native tooling), or at minimum implement
begin/commit/rollback snapshotting and UNIQUE enforcement in the emulation
and make unsupported PRAGMAs/constraints return an explicit error instead of
silent success. Until then, specs should probe transaction honesty first
(insert → rollback → count) and fail closed / classify blocked when the
backend cannot roll back.

## Workaround used by the enterprise store lane

`std.nogc_sync_mut.enterprise_store` runs a self-probe
(`store_backend_capabilities`) at open: it detects non-transactional backends
and reports `acid=false`, and its specs assert application-level invariants
(idempotency replay via SELECT-before-INSERT, audit sha256 chain) that hold
on both backends, while atomicity/constraint specs require `acid=true`.

## Refinement 2026-08-16 (lane W9-B): `--mode=native` is NOT the escape hatch

This bug's earlier resume condition — "run the specs `--mode=native` against
real SQLite" — is **wrong as written**, and acting on it would have produced
falsely-labelled native evidence. Measured on the Rust seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, 59497616 bytes, 2026-08-15):

- The same ACID probe (begin / insert / rollback / count, then a duplicate
  UNIQUE insert) gives **byte-identical non-ACID results under `--mode=native`
  and under the default interpreter**: `after_rollback_count` stays at 49
  (rollback no-op) and `dup_insert_ok=true` (UNIQUE unenforced); `start_count`
  reads 48 on a freshly deleted db file, confirming the per-path in-process
  cache / global counter behaviour already described above.
- `--mode=native` is **in-process JIT**, and its externs resolve to this very
  emulation table (`interpreter_extern/sffi_db.rs`). It is not a different
  backend.
- The seed process contains **no real SQLite at all**:
  `ldd $(readlink -f bin/simple)` shows no `libsqlite3`, and there is no
  `rusqlite`/`libsqlite3-sys` dependency in any `src/compiler_rust`
  `Cargo.toml`. (The "rusqlite is already a seed dependency" premise in the
  Suggested fix section above is therefore **incorrect** — adding it would be
  new work, not a rewiring.)
- Worse for evidence integrity: on `std.nogc_sync_mut.enterprise_store` the
  JIT **silently drops to the interpreter** —
  `[jit-fallback] unresolved external symbol 'store_open': whole module
  dropped to the interpreter`. A `--mode=native` spec run of this module is an
  interpreter run with a native label. `store_backend_acid` returns `false`
  under both modes, as it should.

### Where real SQLite actually lives, and the exact blocker

Real linkage exists only on the **AOT native-project link path**
(`pipeline/native_project/linker.rs:1534`, `tools.rs:1317` -> `-lsqlite3`,
gated by `is_sqlite_runtime_symbol` at linker.rs:500). The host is ready:
`libsqlite3.{so,a}` + `/usr/include/sqlite3.h` installed,
`src/runtime/runtime_sqlite.c` includes the real `<sqlite3.h>`, and
`sh scripts/build/build_simple_runtime_sqlite_sffi.shs` builds
`build/sffi/libsimple_runtime_sqlite_wm.so` cleanly with its own
`rt_sqlite_open` presence assertion passing.

But the reachable single-file route fails:

| command | result |
|---|---|
| `bin/simple compile probe.spl -o probe.exe` | exit 0, but output is `SMF` bytecode (magic `S M F \0`), not an ELF — re-enters the interpreter |
| `bin/simple compile probe.spl --native -o probe` | **exit 1: `error: codegen: undefined symbol: rt_sqlite_open`** (a real lld error parsed at `linker/native.rs:628`) |
| same, after staging the sqlite provider `.so` | **identical failure** — the single-file link line never references it |

**Concrete prerequisite:** teach the single-file `compile --native` link line
to include the `src/runtime/runtime_sqlite.c` object (or the staged
`libsimple_runtime_sqlite_wm.so`) plus `-lsqlite3`, reusing the
`is_sqlite_runtime_symbol` detection the `native_project` linker already has.

**Re-verification command once that lands** (must print the ACID answers, not
the emulation's):

```
bin/simple compile probe.spl --native -o probe && ./probe
# required: after_rollback_count=0   dup_insert_ok=false
```

Only then can rollback-atomicity and constraint-rejection specs be written
honestly; under the emulation both assertions are vacuous in the dangerous
direction (rollback leaves the row; a UNIQUE violation reports success).
