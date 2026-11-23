# Seed native-build: single files take minutes to compile (Windows, full CLI)

Status: open (perf). Found while rebuilding the self-hosted CLI for Lane 8 of
`unit_range_cast_native_execution_blocked_2026-11-19.md`.

Related: `native_build_windows_link_phase_hang_runtime_cache_batch_2026-11-22.md`.
Target in the build policy: the first `.o` within 10 s per file.

## Setup
- Tree: release/1.0.0 at `d83c3a98dc8`, worktree `C:/dev/wt/nv2`.
- Seed: rbnat4's tracked `bin/simple.exe` (38,403,072 B, sha256 prefix `a2e9dd36d0e0f6c2`).
- Command: `SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_INCREMENTAL=1 SIMPLE_NATIVE_FILE_TIMING=1
  seed.exe native-build src/app/cli/main.spl -o build/nv2/cli_main.exe --cache-dir build/nv2/cache
  --timeout 3600 --threads N` (llvm-mingw UCRT on PATH). About 4,100 files.

## Measured (2026-11-23, shared host)
| file | wall | cpu |
|---|---|---|
| `src/app/bug/workaround_store.spl` | 1689.3 s | 1685.5 s |
| `src/app/buildrunner/remote_container_reset_failure_v3.spl` | 452.8 s | 451.6 s |
| `src/app/cli/dispatch/table.spl` | 307.3 s | 292.0 s |
| `src/compiler/35.semantics/lint/_SimdOpportunityLint/byte_checks.spl` | 290.7 s | 280.2 s |
| `src/lib/common/json/value.spl` | 279.5 s | 269.3 s |
| `src/compiler/10.frontend/core/__init__.spl` | > 300 s (timed out) | - |

Wall is close to CPU, so the time goes into compute, not into waiting on locks or I/O.
Rate with 16 threads: 136 -> 360 objects in 1h55m (about 120 objects/h). At that rate
the full CLI takes about 30 h.

## Seed A/B (same entry file, run at the same time, `--threads 1`)
`src/app/cli/main.spl` per-file timing:
- Seed A, rbnat4 `bin/simple.exe` (build-commit `1343b77bbaa`, 11-17): 202.3 s
- Seed B, `C:/dev/simple/bin/simple.exe` (sha256 prefix `d1e16e3da724b4d9`, build-commit `f3e12b05d39`, 11-19): 87.8 s

That is 2.3x, so the CLI rebuild switched to seed B. The per-file cost is still far above 10 s.

## Side defects found on the same run
1. The default per-file timeout is 300 s (`DEFAULT_NATIVE_FILE_TIMEOUT_SECS`). After the first
   timeout, every remaining file reports `NOT_ATTEMPTED: previous native worker timed out;
   refusing replacement admission` (`native_project/compiler.rs:1145`). One slow file fails the
   whole build: 4,099 of 4,100 files were never tried.
2. On the llvm backend the default worker count is `min(cores, 4)` (`LLVM_DEFAULT_MAX_THREADS`)
   unless `--threads` or `SIMPLE_BOOTSTRAP_THREADS` is set.

3. With seed B (48 threads: 4,099 of 4,100 files in 27m17s), one file failed to compile:
   `src/lib/nogc_sync_mut/test_runner/test_db_compat.spl:394`. The HIR error was `call to
   TestDatabaseExtended.add_timing_run omits argument 5 whose default is not a call-site constant`.
   The default is the enum variant `TestBaselineEligibility.Eligible`. The rebuild passed it
   explicitly as an uncommitted, build-only workaround tagged `WA(nv2)`. The release tree is
   unchanged. Fix candidates: treat an enum-variant default as a call-site constant in the seed,
   or pass the argument explicitly in the source.
   Fix (verification-pending, branch `work/ed1-20261123`): enum-variant defaults are legal
   (63 `.spl` files use them), so the seed now treats a payload-free `E.V`/`E::V` default as a
   call-site constant (`is_unit_enum_variant`, `hir/lower/expr/calls.rs`). Needs a seed rebuild.

## Next
Profile one slow file (`workaround_store.spl`) through parse/HIR/MIR/LLVM phases to find the
superlinear phase. The Lane 8 report may add seed A/B timings.

## Seed B, full CLI, 48 threads
4,100 files in 27m17s, so the 1,689 s outlier did not recur. The final composition build
(4,125 files) took 31m00s. Per-file cost still runs to minutes on some files, against the 10 s target.
