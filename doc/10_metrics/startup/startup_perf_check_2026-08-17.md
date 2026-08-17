# Startup Perf Check — 2026-08-17 (Phase D evidence)

Slice per `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md`.
Verdict up front: **all measured startup cost is Rust-seed-side; no pure-Simple
startup-path win exists to land.** This is the honest no-.spl-win report with data.

## Environment / binary identity

- `readlink -f bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
  (59,537,240 bytes, mtime 2026-08-17 12:58:51 UTC)
- `--version` banner: "WARNING: this Rust-built Simple binary is a bootstrap
  seed only…" — **Rust seed**, as predicted.
- Load average during measurement: 0.71–1.38 (1-min), shared box.

## p50 wall time (10 runs each, warm, /usr/bin/time %e)

| command | p50 | samples |
|---|---|---|
| `bin/simple --version` | **0.05 s** | 0.05 0.05 0.06 0.05 0.05 0.06 0.05 0.06 0.05 0.06 |
| `bin/simple run hello.spl` (scratchpad, `print("hello")`) | **0.06 s** | 0.05 0.05 0.06 0.05 0.06 0.06 0.06 0.06 0.06 0.06 |

Startup is already ~50–60 ms end-to-end on this seed.

## Syscall trace (strace -f -c)

| syscall | `--version` | `run hello.spl` |
|---|---|---|
| statx | **10,642** | 19 |
| openat | 14 | 14 |
| mmap | 30 | 35 |
| read | 9 | 21 |
| close | 151 | 158 |

Notable observations:

1. **statx storm on `--version` (10,642 calls)** — 10,145 hits on
   `.simple/logs/crash_N.log` plus 460 on stale `.simple-log-probe-N` files.
   Cause: `cleanup_old_logs` in
   `src/compiler_rust/driver/src/cli/../log.rs` (seed) does
   `read_dir(.simple/logs)` and calls `path.is_file()` (a statx) on **every**
   entry *before* filtering on the `simple.log` name prefix. The workspace has
   accumulated 10,145 `crash_*.log` + 460 stale probe files, so log-dir init
   stats ~10.6k paths per invocation. **Seed-side (Rust) — out of scope for
   this slice.** Cheap fixes for a seed owner: filter by file name before
   stat; or prune the crash-log/probe backlog. Note the storm did not fire on
   the `run` path in this trace (statx=19), so it does not currently affect
   the hello p50; it is latent cost tied to logs-dir size.
2. **hello.spl opened/statted 5 times per run** — seed-side duplicate reads of
   the entry file in the CLI path. Small at this file size, avoidable.
3. **`src/lib` opens: 0** for the hello run. The documented "82 src/lib opens
   per run" baseline did not reproduce for an import-free script — stdlib
   loading is evidently lazy on this seed build. No .spl-side I/O above
   baseline exists to remove.
4. Each run stats `.simple/native-objects-*` temp dirs (35 present) and
   `doc/08_tracking/{bug,feature,task,test,todo}` — seed-side, ~45 statx, noise
   at this scale.

## Pure-Simple startup path review

- `src/app/startup/host_startup.spl` (144 lines): pure functions — manifest
  arg-schema parse + preload orchestration. **Zero eager I/O, zero env/config
  reads, zero duplicate reads.** The only file I/O (`preload_readonly_file`)
  is manifest-declared and single-shot per spec entry. Only inefficiency is an
  O(n·m) `_startup_argument_present` scan over declared-schema-sized lists
  (single digits) — micro-optimizing it would be unmeasurable against a 50 ms
  process and would violate the no-over-engineering rule.
- `src/app/startup/dynsmf_autoload.spl` (read-only, not owned): no startup I/O
  issue observed in traces.
- This file is not on the seed's `--version`/`run hello` hot path at all; its
  costs are exercised by the SimpleOS/manifest launch flow.

## Evidence spec

`test/02_integration/app/startup_argparse_mmap_perf_spec.spl`
(SIMPLE_TIMEOUT_SECONDS=900):

Ran to completion (exit 0):

```
SPEC FILE VERDICT: test/02_integration/app/startup_argparse_mmap_perf_spec.spl declared>=2 executed=2 passed=2 failed=0 dropped=0
Results: 2 total, 2 passed, 0 failed
```

## Conclusion (Phase D)

- p50 startup: 0.05 s (`--version`) / 0.06 s (hello run), Rust seed.
- Top cost above noise: the 10.6k-statx log-dir scan on the `--version` path —
  100% seed-side (`driver/src/log.rs` `cleanup_old_logs` stat-before-name-filter
  plus a 10.6k-file logs backlog). Second: 5x duplicate open of the entry file —
  seed-side CLI.
- Pure-Simple startup code (`host_startup.spl`) performs no avoidable work;
  **no .spl-side change is justified by measurement**, so per the plan this
  report is the deliverable. Recommended follow-ups for seed owners: name-filter
  before stat in `cleanup_old_logs`; prune/rotate `crash_*.log` and stale
  `.simple-log-probe-*` files.
