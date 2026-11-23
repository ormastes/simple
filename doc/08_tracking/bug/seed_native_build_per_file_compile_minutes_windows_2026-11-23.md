# Seed native-build: single files take minutes to compile (Windows, full CLI)

Status: verification-pending (pre_hir root cause fixed, branch `work/pf1-20261123`; hir phase still open). Found while rebuilding the self-hosted CLI for Lane 8 of
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
   Fix (natively verified 2026-11-23, PR #10999): enum-variant defaults are legal
   (63 `.spl` files use them), so the seed now treats a payload-free `E.V`/`E::V` default as a
   call-site constant (`is_unit_enum_variant`, `hir/lower/expr/calls.rs`). Needs a seed rebuild.

## Next
Profile one slow file (`workaround_store.spl`) through parse/HIR/MIR/LLVM phases to find the
superlinear phase. The Lane 8 report may add seed A/B timings.

## Seed B, full CLI, 48 threads
4,100 files in 27m17s, so the 1,689 s outlier did not recur. The final composition build
(4,125 files) took 31m00s. Per-file cost still runs to minutes on some files, against the 10 s target.

## Native verification of the enum-default fix (2026-11-23, sd1)
The seed was built from `origin/release/1.0.0` @ `84ea108c7c9` (includes #10999 and `7f610c22789`) with
`cargo build --release --bin simple` (clang-cl, Windows). The binary's sha256 prefix is `a72695a600b21163`.

| Check | Result |
|---|---|
| `compile src/lib/nogc_sync_mut/test_runner/test_db_compat.spl`; the call at `:399` omits arg 5, no `WA(nv2)` | PASS, rc=0, 4.8 MB `.o`, 0 "call-site constant" errors |
| `native-build` of a minimal fixture (`fn pick(a, e: Elig = Elig.Eligible)`, called as `pick(41)`), then run | PASS, linked via llvm-mingw, prints `r=42` |
| `default_param_enum_variant_fill_spec` | PASS 3/3 |
| `unit_div_remainder_native_spec` (sanity) | PASS 8/8 |

The enum-default item (3) is verified. The per-file slowness this bug tracks remains open.
## Root cause 1 (pf1, 2026-11-23): `pre_hir` = `build_use_map_from_ast`
`workaround_store.spl` alone (94-file closure) compiles in 1.2 s; per-file cost scales with the
closure. On the full CLI closure, `SIMPLE_NATIVE_FILE_TIMING=1` showed `pre_hir` was 65 % of all
per-file CPU (20,977 of 32,246 s), up to 190 s for `src/compiler/10.frontend/core/__init__.spl`.
`pre_hir` is dominated by `build_use_map_from_ast` (`native_project/imports.rs`): for every
`Single` import it walked the whole `all_mangled` table twice (module-qualified `name.fn` keys,
and the bare multi-candidate keys), calling `resolve_import_name_strict` per key, which re-did
the `use_segments` joins, two re-export lookups and five family `format!`s every time. Cost was
O(imports x table) with ~10 allocations per step, so re-export hubs (`__init__.spl`, `mod.spl`)
took minutes.

Fix (seed, Rust): `StrictImportScope` hoists the per-path work out of the loop; the module-qualified
scan visits only keys indexed under the imported name (lazy part index, same normalisation as
`mangled_matches_use_path`) plus re-export entries; the bare multi-candidate scan runs once per
use path instead of once per group item. Regression check:
`build_use_map_wide_closure_stays_within_budget` (`native_project/tests.rs`).

Seed built from this tree, full CLI, `--threads 40`, same host, fresh cache each run:

| seed | wall | pre_hir CPU sum / max | hir CPU sum / max | files > 10 s | max file |
|---|---|---|---|---|---|
| `C:/dev/simple/bin/simple.exe` (before) | 26m37s | 20,977 s / 190 s | 9,097 s / - | 869 | 390 s |
| intermediate (scope hoist only) | 24m35s | 11,143 s / 223 s | 9,507 s / 130 s | - | 223 s |
| fix | 22m02s | 3,063 s / 9.6 s | 10,558 s / 141 s | 324 | 145 s |

`core/__init__.spl` 191 s -> 6.0 s, `app/io/mod.spl` 120 s -> 5.4 s, `workaround_store.spl` 2.9 s.
All 4,101 files compiled, 0 failed. Peak process RSS (one process, 40 worker threads, 1 s sampling):
intermediate 6.9 GB, fix 7.6 GB (+0.7 GB: one lazy part index per file worker). The before-seed
RSS was not sampled on this run.

## Still open: `hir` phase
`lower_module_with_return_types` is now the dominant cost (10,558 CPU s, up to 141 s per file,
e.g. `app/io/_CliCommands/handler_commands.spl`, `app/build/cli_entry.spl`). Wall to end of build
is also bounded by the tail of these files. Next: profile HIR lowering against the global
struct/fn-return/enum tables for the full closure.
