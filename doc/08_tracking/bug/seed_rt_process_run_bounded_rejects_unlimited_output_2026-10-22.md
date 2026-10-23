# Rust seed `rt_process_run_bounded` rejects `-1` (unlimited output); `simple test` cannot run any spec on Windows
## Open 2026-10-22 — needs owner triage

**Found:** 2026-10-22, lane `wt-sqlite-format-20261022` (work/sqlite-format-reader-20261022),
while bringing up unit specs for `std.nogc_sync_mut.database.sqlite_format`.

## Symptom

Every `bin/simple test <spec.spl>` invocation — including a one-assertion trivial
spec — dies before executing a single example:

```
error: runtime: rt_process_run_bounded: max_output_bytes must be a non-negative integer
```

The same spec runs green via `bin/simple run <spec.spl>`.

## Cause

`src/lib/nogc_sync_mut/io/process_ops.spl` `_process_run_raw` documents and
implements the bounded-ABI contract on Windows:

```simple
# The bounded owner uses CreateProcess and GetExitCodeProcess; timeout 0
# means none and -1 means unlimited output, the same as rt_process_run.
if _is_windows_platform():
    unsafe(capabilities: [ffi]):
        return rt_process_run_bounded(host_path_native(rcmd), rargs, 0, -1)
```

`-1` = "unlimited output" is the source-level contract. The Rust seed binary
(`bin/simple.exe`, v1.0.0-beta.11) validates `max_output_bytes` as a
non-negative integer in its native `rt_process_run_bounded` and aborts the
process on `-1`. The pure-Simple runtime (built via bootstrap) accepts `-1`;
only the seed is stricter than the source contract.

The failure is reached from the spec runner's environment/evidence path, which
calls the unbounded `process_run` → `_process_run_raw` → seed abort. So no
spec can be executed through `simple test` with the seed on Windows.

## Workaround used by the sqlite-format lane (minimal, no source change)

Run specs directly through the interpreter entry instead of the test runner
worker path:

```bash
bin/simple run test/01_unit/lib/database/sqlite_format/<name>_spec.spl
```

`std.spec` (`describe`/`it`/`expect`) executes at program start and prints the
same per-example results plus a `SPEC FILE VERDICT ... passed=N failed=N` line,
so Failed: 0 is observable without the worker machinery. Anything needing a
subprocess from inside a spec (e.g. the python sqlite3 differential oracle)
must use the bounded variant `process_run_bounded(cmd, args, timeout_ms,
positive_cap)` — never the unbounded `process_run` — to stay off the broken
path.

## Proper fix (out of this lane's ownership)

Align the seed's `rt_process_run_bounded` validation with the source contract
(accept `-1` as unlimited, matching `rt_process_run`), or route
`_process_run_raw` through a positive cap. Owned by whoever owns
`src/compiler_rust` runtime shims; `src/lib/nogc_sync_mut/io/process_ops.spl`
must not be weakened to work around a seed-only validation bug.
