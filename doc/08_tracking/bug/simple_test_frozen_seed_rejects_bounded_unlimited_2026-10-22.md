# `bin/simple test` unusable in this worktree: frozen Rust seed rejects `-1` max_output_bytes (workaround: `bin/simple run <spec>`)

- **Filed:** 2026-10-22
- **Status:** NOT A NEW DEFECT — environment instance of
  `doc/08_tracking/bug/seed_process_run_bounded_rejects_unlimited_2026-09-26.md`
  (FIXED in source; this worktree's `bin/simple.exe` is the pre-fix frozen
  Rust bootstrap seed, `Simple Language v1.0.0-beta.11`).
- **Host:** Windows 11, x86_64-pc-windows-msvc
- **Worktree:** `C:/dev/wt-cipher-d-profile-20261022`

## Symptom

Every `bin/simple test <spec>` invocation — including untouched, previously
green specs such as
`test/01_unit/lib/database/database_stats_spec.spl` — aborts before running a
single example with:

```
error: runtime: rt_process_run_bounded: max_output_bytes must be a non-negative integer
```

## Cause

The `simple test` runner (safe mode) spawns the spec via
`process_run_bounded(binary, ["run", path], timeout_ms, ...)`, which on
Windows routes through `rt_process_run_bounded(..., -1)`. The frozen seed
binary rejects `-1`; the fix exists in
`src/compiler_rust/compiler/src/interpreter_extern/system.rs` but the seed has
not been rebuilt/re-admitted in this worktree. Rebuilding the seed is a
bootstrap-lane action (out of scope here; full bootstrap runs are excluded
from this lane's constraints).

## Minimal workaround (used for this lane's specs)

Run the spec directly — this is exactly the child process the runner would
spawn, minus the broken wrapper:

```bash
bin/simple run test/01_unit/lib/database/codec/sqlcipher4_profile_spec.spl
bin/simple run test/01_unit/lib/database/codec/codec_registry_spec.spl
```

Pass gate: the `SPEC FILE VERDICT` line reports
`outcome=OK ... failed=0` and the process exits 0. Both lane specs pass
37/37 and 10/10 examples this way (2026-10-22).
