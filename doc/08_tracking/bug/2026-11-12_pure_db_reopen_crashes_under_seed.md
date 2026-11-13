# Pure-database reopen paths crash or refuse under the seed runtime (blocks process-backed DB specs)

- **Date:** 2026-11-12
- **Status:** OPEN (root-caused to the seed/runtime boundary; needs the C-runtime or self-hosted binary to confirm/fix)
- **Severity:** High — data-plane corruption class (writer commits, reader crashes)
- **Area:** `src/compiler_rust` seed externs (`sqlite_sffi`, pure-db codec interaction), `src/lib/nogc_sync_mut/database/pure_sql/`

## Finding 1 — spawned reader crashes with STATUS_STACK_BUFFER_OVERRUN

`context_store_v1_recovery_runner.spl` / `pure_sql_reopen_process_runner.spl`,
spawned as `bin/simple run <runner> read <db>` after a successful writer
commit:

```
expected -1073740791 to equal 0        # 0xC0000409 STATUS_STACK_BUFFER_OVERRUN
expected  to contain CONTEXT_STORE_READER_REOPENED rows=3 ids=2,7,8
```

The writer phase completes (`CONTEXT_STORE_WRITER_COMMITTED rows=3` observed);
every reader/publish spawn then dies with the Windows stack-overrun crash
code. Reproduced 2026-11-12 in the pq1 phase-2 worktree
(`work/product-queue-p1-20261112`) with the phase2 seed binary on a Windows
host; fixture paths anchored under `get_temp_dir()`.

## Finding 2 — `sqlite_sffi` create-then-reopen asymmetry

`context_pure_database_import_runner.spl prepare` reports
`CONTEXT_IMPORT_SOURCE_READY` (its `context_sql_put_pack` returns
`status: ready`), and the file on disk is 454 bytes beginning with the
`simple-pure-db-v3` header — but a subsequent `sqlite_open` of the same file
returns `is_valid=false` and `sqlite_table_exists(db, "context_packs")=false`.
The facade can create a table through the seed's sqlite externs yet cannot
reopen it, so `context_sql_db_format` (added in this lane, honestly) reports
`unknown` and `context_sql_import_facade_to_pure_v2` refuses with
`source_format_not_supported`.

## Finding 3 — constant `1/0` crashes the seed with STATUS_ILLEGAL_INSTRUCTION

`run_diagnostics_contract_spec.spl` ("prints stable division by zero code and
help") expects `error[E2001]` + help with exit 1. The seed instead exits
`-1073741795` (0xC000001D STATUS_ILLEGAL_INSTRUCTION) while JIT-compiling
`fn main(): val x = 1 / 0`. The undefined-function case (`error[E1002]`)
renders correctly; only the constant-fold division crashes.

## Affected queue specs

- `test/02_integration/app/context_store_v1_recovery_spec.spl` (3/5 examples
  blocked; the two rejection-only examples pass)
- `test/02_integration/app/pure_sql_reopen_process_spec.spl` (4/4 blocked)
- `test/02_integration/app/context_pure_database_import_spec.spl` (import and
  verify modes blocked; prepare passes)
- `test/02_integration/app/diagnostics/run_diagnostics_contract_spec.spl`
  (E2001 case blocked; E1002 and E0001 render — E0001 via a different
  engine-demotion message than the pinned stable text)

## Fix direction

Reproduce under the C runtime / self-hosted binary (`bin/release/.../simple`)
to separate seed-only defects from genuine pure-Simple defects. If the crash
reproduces on the self-hosted binary, audit the pure-db reader for unbounded
recursion (codec page walk / schema resolution) — a stack-overrun on reopen
of a 454-byte fixture is a logic bug somewhere in the frame chain, not a
depth-limit policy.
