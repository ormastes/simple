# Verification of ae5401713a9 import-re-export risk: BLOCKED (inconclusive)

Date: 2026-08-18

## Task
Verify whether downstream `use std.X.file_ops.{file_delete, file_copy, dir_walk}`
imports still resolve correctly now that commit `ae5401713a9` deleted the local
wrapper *definitions* of `file_delete`/`file_copy`/`dir_walk` in:
- `src/lib/nogc_sync_mut/io/file_ops.spl` (deleted `file_delete`, `file_copy`;
  both now only `use std.io_runtime.{read_file_text, file_delete, file_copy}`)
- `src/lib/nogc_async_mut/io/mod_stub.spl` (deleted `file_delete`, `file_copy`, `dir_walk`)
- `src/lib/gc_async_mut/file_system/file_ops.spl` (deleted `file_delete`; now
  `use std.io_runtime.{file_write, file_delete}`)
- `src/lib/gc_async_mut/io/mod_stub.spl` (deleted `dir_walk`; now
  `use std.io_runtime.{dir_exists, dir_walk}`)

## Importer census (src/ + test/, grep for `io.file_ops.{`, `file_system.file_ops.{`, `io.mod_stub.{`)
~50 importers found; ~30 import a deleted symbol (`file_delete`/`file_copy`)
directly from `nogc_sync_mut.io.file_ops` or transitively via
`gc_async_mut.io.mod_stub` -> `gc_async_mut.io.file_ops` ->
`nogc_sync_mut.io.file_ops`. Full list captured in session transcript; notable
consumers: `src/lib/nogc_sync_mut/db_atomic.spl`, `oauth2.spl`,
`test_runner/test_result_wrapper.spl`, `test_runner/test_runner_async.spl`,
`src/compiler/70.backend/backend/llvm_backend.spl`, `src/app/io/mod.spl`, and
~15 spec files under `test/01_unit`, `test/02_integration`, `test/03_system`.

## Result: could not execute ANY covering spec

Every attempted `bin/simple test <spec>` — including
`test/01_unit/db_atomic_hir_contract_spec.spl` (the one the task description
says passed 2/2 previously) and `test/01_unit/lib/database/database_atomic_spec.spl`
— fails identically at COMPILE time, before reaching the code under review:

```
error: compile failed: parse: in ".../src/lib/nogc_sync_mut/io/env_ops.spl": Unexpected token: expected Comma, found Colon
```

Root cause: `src/lib/nogc_sync_mut/io/env_ops.spl:8` currently reads
`use std.io_runtime.{process_run, env_set: io_env_set}` — a `name: alias`
import-rename form. Grepped the whole of `src/lib` for this syntax
(`use std\..*\.{.*: .*}` and `... as ...}`) — **zero other occurrences**,
confirming the parser genuinely does not support it; this is not a resolver
edge case. Introduced by a **different, later** commit `94afb1dd7d6`
("refactor(rt): spipe cycle track B — rt_ externs -> std.io_runtime wrappers
in 48 file(s)", 2026-08-18 02:26:32 +0000), not by `ae5401713a9`. `env_ops.spl`
is imported transitively by essentially every `io`/`file_ops` consumer, so this
single syntax error currently blocks compilation of the whole io stack —
independent of and unrelated to the specific wrapper-deletion risk under review.

## Verdict

**INCONCLUSIVE, not verified safe or unsafe.** The specific misdispatch risk
from `ae5401713a9` (deleted wrapper definitions vs. re-exported imports) could
not be exercised because an unrelated, later regression in
`src/lib/nogc_sync_mut/io/env_ops.spl` (commit `94afb1dd7d6`) currently blocks
compilation of every module that transitively imports `io/env_ops.spl`,
including every file_ops/mod_stub consumer tried. No repair was made to
`ae5401713a9`'s deleted wrappers because the safety question remains untested,
and no fix was applied to `env_ops.spl` because it is out of scope for this
review (different commit, different concern). Recommend: fix
`env_ops.spl:8`'s invalid import syntax first (blocking bug, filed here), then
re-run this verification.
