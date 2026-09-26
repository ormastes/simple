# native-build stall pattern (mcp closure, aarch64 host, 2026-09-25)

Four attempts to native-build the simple_mcp_server closure (2026-09-24/25), zero completions:
1. Clean-worktree pair: died silently at 'execute main start' (~2h).
2. Replacement pair: 6h parked (all threads futex-wait, RSS 13.7GB, CPU plateau).
3. Main-worktree build: died silently ~12 min in (log tail = collision warnings, no error, no EXIT).
4. Main-worktree rebuild: 4h54m wall; CPU time FROZE at 03:46:12 (~6s of CPU in the final 3.5h) — parked threads, RSS 360MB, zero output.

Pattern: the build reaches a post-codegen phase ('[rust-jit] execute main' / link) and its threads park on futexes permanently. No error, no EXIT line, no output binary. The other-lane reroot closure (pid 488914) DID finish in 52 min on the same host/binary, so this is closure- or phase-specific, not universal.

Working alternatives verified meanwhile: interpreter mode (bin/simple run src/app/mcp/main.spl) passes initialize + stdio specs; deployed Sep-6 native binaries answer --version + initialize but fail the wrapper's strict native probe.

Next compiler-lane action: attach a debugger to the parked phase (gdb -p on a fresh stall, thread apply all bt) to find the futex owner; suspect the JIT-execute/link driver lock or the SCV snapshot walk deadlock.

## Attempt 5 (2026-09-25 08:56 → 11:01, pid 1060977, codex/spipe-local-knowledge-setup lane)

- Command: `setsid nohup env SIMPLE_SCV_INVENTORY_COLD_INIT=1 SIMPLE_TIMEOUT_SECONDS=0 bin/simple native-build --source src/compiler --source src/app --source src/lib --entry-closure --entry src/app/mcp/main.spl --threads 10 --strip --output build/bootstrap/mcp-package/simple_mcp_server` (log `/tmp/mcp-main-build3.log`, 185 lines).
- Wall 2h04m40s; CPU 2h03m26s — ~100% one core for the ENTIRE run, no plateau, no park (main thread never futex-waited; unlike attempts 2/4 it did not spawn a long-lived parse shard either). RSS stayed 0.4–1.4 GB (never ballooned; attempt 4 had hit 17.3 GB).
- New failure mode — explicit, non-silent: final log lines are an `export use *` style warning then
  `SCV-E-ADMISSION: filesystem-event-journal-missing (clear build/scv and .scv, then rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)`.
  No output binary. `SIMPLE_SCV_INVENTORY_COLD_INIT=1` WAS set in the process env; `build/scv/source-inventory` exists, repo-root `.scv` does not.
- Same-window context: the sibling /tmp checkout's lsp build failed at link with 3 missing runtime symbols (`rt_array_is_byte_packed`, `rt_enum_check_variant`, `rt_is_present`) — all three ARE defined in the current repo `src/runtime/runtime_native.c`, so that link failure is a stale-checkout artifact, not this closure.
- Host facts for diagnosis: 20 cores, load ~5 (no CPU starvation; the "parked" attempts 2/4 co-existed with 100%-CPU helper shards). `/tmp/kill_simple_monitor.log` heartbeats stopped 2026-09-24 22:12 — the runaway killer daemon was NOT the silent-death cause.
- Not relaunched (parent directive); remediation hint recorded for whoever picks it up: clear `build/scv` (and any `.scv`) then rerun with `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.
