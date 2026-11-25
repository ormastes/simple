# Native Pool Loop Closure Capture Fanout Mismatch

## Closed 2026-09-13 — Recorded fixed in the entry body

- **inferred** Status `likely-fixed (triaged 2026-06-11)` with resolved/fixed content in the body.
- **measured** No surviving broken product path is named (path scan: 0 backticked source paths).
- **measured** The native lane cannot be re-run here: `bin/simple compile --native` fails with `ld: cannot find -lsimple_runtime` / `ld: cannot find -lc`.
- **inferred** Closing on the recorded fix; re-file with a native transcript if pool-loop capture fan-out misbehaves again.


Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below

## Summary

Generated multicore-green fanout workloads that submit escaped runtime-pool
closures from a loop previously captured the loop seed incorrectly in native
builds. This is fixed for the current hosted native path.
The workload shape:

```spl
for seed in 0..1000:
    handles.push(multicore_green_spawn(\: work(seed)))
```

compiled and ran with `pool_used=1000/1000`, but produced checksum mismatches
before the fix.
Wrapping the closure in `spawn_work(seed_copy)` still mismatched, which means the
escaped closure environment is not preserving the per-call value strongly enough
for the runtime-pool handoff.

## Evidence

### Original Failure

- `build/cross_lang_perf/fanout_multicore_green_simple_native` printed
  `multicore_green_pool_used = 1000/1000` followed by checksum mismatch.
- `build/cross_lang_perf/fanout_stress_multicore_green_simple_native` printed
  `multicore_green_pool_used = 512/512` followed by checksum mismatch.

### Fixed Evidence

`SIMPLE_BINARY=./src/compiler_rust/target/debug/simple RUNS=1
REPORT_PATH=doc/09_report/cross_language_perf_parallel_smoke.md sh
scripts/check/check-cross-language-perf.shs` now reports
`profile_report_contract=true` with compact loop-submitted fanout closures:

- `Simple multicore green (native)` fanout: `pool_used=1000/1000`,
  `parallelism=64/64`.
- `Simple multicore green (native)` stress fanout: `pool_used=512/512`,
  `parallelism=64/64`.

## Resolution

Native closure creation now uses runtime heap allocation instead of stack
allocation, and outlined lambda functions materialize captured values as real
capture locals hydrated from the closure context. The profile generator again
uses compact loop submission, so checksum validation covers loop-local capture.

## Verification 2026-11-25 — closure stands (code inspection; native re-run environment-blocked)

Checked on Windows worktree `D:\wt-p3-bae` (branch `work/p3-bae-20261125`,
base `origin/release/1.0.0`):

- The recorded resolution is still present in current source:
  `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:9035-9038`
  documents and implements capturing lambdas using "the runtime closure handle
  as a heap environment" with the lifted function receiving the handle as a
  hidden first argument, and unsupported capture shapes failing loudly rather
  than building a partial environment. This matches the "runtime heap
  allocation + real capture locals hydrated from the closure context"
  resolution above.
- The native lane cannot be re-run on this host: `bin/simple.exe compile
  --native` on a hello-world probe fails in `lld-link` (temp-path/argument
  handling on Windows), so the fanout checksum evidence could not be
  re-collected here. Verification is by code inspection plus the recorded
  2026-09-13 fixed evidence; this limit is stated explicitly.

Status remains closed.
