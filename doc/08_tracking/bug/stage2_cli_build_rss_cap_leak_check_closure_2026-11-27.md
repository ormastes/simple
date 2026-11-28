# Stage 2 CLI build exceeds 60 GiB RSS cap (1551-module leak_check closure)

- **Status:** open. Admission margin hardened (see Root cause and change); a first run of a new producer can still reach the cap
- **Found:** 2026-11-27, bootstrap of pinned `967f9178950e` (release/1.0.0 head)
- **Evidence:** Rust seed-built Stage 2, bootstrap verification campaign. Diagnostic only.

## Symptom
`stage2-compiler-tests` ABORTED during `compiler_cli_build` after about 3.5 h:
`primary_status=rss-cap-exceeded`, `rss_limit_kib=62914560`
(in `logs/aarch64-unknown-linux-gnu/stage2-compiler-tests.log`).
The tree RSS went from 55 GB to 62 GB in the last 60 s. The last progress line was
`phase=hir ... done=1119 total=4204 succeeded=513 cached=606 failed=0`. There were no error lines.

## Cause (diagnosed from logs; not reproduced)
- **Two workers live together.** Both file workers stayed alive for the whole run, at 18–29 GB RSS each.
  In the earlier pin `3dd00937c329`, owner 1 died on
  `FILE-WORKER-E-CLOSURE-INCOMPLETE` (fixed by #12126), so that run used one worker from there on and
  never reached this point.
- **One unusually large unit.** Owner 1 picked a unit with a
  `mir-child hir closure modules=1551 of=7187` (log line 639742); every other
  unit across four pins tops out at 432–549 modules. The unit covers `app/devhub/*`,
  `compiler/90.tools/leak_check/*` and `mem_tracker`. It lowered 513 modules fresh; normal units lower 1–16.
- **The import behind it.** `src/compiler/90.tools/leak_check/external_runner.spl:9` has a plain
  `use compiler.driver.driver_api_codegen_backends.{aot_c_file}`, which pulls in most of the
  driver for one function. Only 12 of the 1189 lowered modules are braced re-export facades, so
  #12126 did not enlarge the closure. The import is the same at `3dd00937c329`.
- **Breach mechanism.** Two workers at about 27 GB, plus a new MIR child started by owner 0 in the final 29 s,
  together exceeded the 60 GiB tree cap. This is an inference: the `rss.env` files hold only tree totals.

## Root cause and change (2026-11-27)
The pool read the right limit and the wrong price.
- **Limit.** The row exports `SIMPLE_SHARD_TREE_MEMORY_BUDGET_KIB=62914560`, the same figure the
  watchdog enforces (`rss_limit_kib=62914560`). Admission and watchdog agree on the cap.
- **Price.** `scripts/bootstrap/lib/product-frontend-policy.shs:44,92` exports
  `SIMPLE_HIR_SHARD_WORKER_KB=9000000` on every fanout host. The compiler treats that as an explicit
  override, logged as `[hir-shard] admission worker estimate=9000000 kB` (log line 12637).
  At 9 GB two workers fit 60 GiB on paper; the real pool needs far more (records below).
- **An override switched off both margins.** `shard_commit_unmeasured_estimate_kib_v1`
  (`src/app/cli/shard_mem_clamp.spl`) doubles the price while unmeasured and adds 25% to a
  recorded peak, but under an override it did neither. A recorded peak up to half the worker
  budget (30553426 KiB here) therefore re-admitted two workers.
- **Change.** Under an override the recorded peak now keeps its 25% margin, with the override as
  a floor. Under this cap a record above 24442740 KiB admits one worker at a time (the second
  slot starts when the first worker exits); a 12 GB or 24 GB record still admits two.
  Red/green on the pure admission model: `test/01_unit/app/cli/shard_peak_persistence_spec.spl`
  and `shard_commit_admission_spec.spl`.
- **What this does not show.** Whether it would have changed the second run is unknown: the only
  record for this pin was written at 16:31 by the second run itself, so the record present at its
  13:32 admission (if any) is not recoverable. The old code already refused a second worker for a
  record above 30553426 KiB, so the change matters for records between 24.4M and 30.6M KiB.
  No bootstrap was run.

## Recorded pool peaks (file-worker, stage2-compiler-tests caches, KiB)
`06ba866385d5` 47550100 and 39356044; `3dd00937c329` 54247532 and 14556356; `967f9178950e` 63498886;
`e803fa9762cd` 15912940 and 13019388; `f43f68c218ef` 32617076 (still running).
The record is a host commit delta split over live workers, so neighbours inflate it
(63498886 is above the whole tree cap). Five of eight are over 3.5x the 9 GB override.

## Still open
- **First run of a new producer.** The record is keyed on the compiler binary and lives in the
  per-candidate cache, so a new pin starts with no record and the 9 GB override admits two workers.
  That run can still reach the cap. Closing this needs either a truthful static price for the
  full-CLI file-worker pool (per-process peaks are not in the receipts, only tree totals) or a
  price per unit (the 1551-module closure is known only inside the unit child, and nothing
  carries it across workers).
- **Start-time count.** `shard_worker_estimate_kib_v1` still lets an override hide the record, so
  the log prints `workers=2` even when spawn admission runs them one at a time.
- **Sticky serial.** The record only grows. A noise-inflated record keeps a pool serial until the
  `.peak_kib` file is deleted, and a serialised pool runs under a row timeout scaled for two.

## Workaround
`BOOTSTRAP_VERIFY_MODULE_WORKERS` does not govern this row: it is read only for the
`module_compile_*` rows (`scripts/bootstrap/bootstrap-phase-verification.shs:1986`). The row's
worker count is `--threads`, from `BOOTSTRAP_VERIFY_BUILD_THREADS` (requested at
`scripts/bootstrap/bootstrap-from-scratch.sh:6212`, fitted by the tree RSS plan); `1` is that
plan's documented one-worker route. Not exercised in this investigation.

## Fix options (owner)
1. Narrow `leak_check/external_runner.spl` so it does not import `driver_api_codegen_backends`
   for `aot_c_file`, for example by moving the helper to a leaf module.
2. Have the file-worker planner bound or split a unit whose HIR closure is more than about 2× the usual maximum.

## First-run fix (2026-11-27)
`scripts/bootstrap/lib/product-frontend-policy.shs` priced a Linux HIR worker at
9 GB (`SIMPLE_HIR_SHARD_WORKER_KB=9000000`), but `compiler_cli_build` HIR workers
measured 18–30 GiB. The Linux branch now prices HIR at the measured 30 GiB
(`31457280` KiB), just as parse was already repriced to 24 GiB. Under the 60 GiB cap,
that is above the half-budget line (30553426 KiB), so the pool admits one HIR
worker even on a pin's first run, when there is no peak record yet. Policy output on
this Linux host: `SIMPLE_HIR_SHARD_WORKER_KB` was 9000000 and is now 31457280.
The bootstrap policy tests `product-frontend-policy-test` and
`phase-c-frontend-policy-test` already fail on Linux before this change,
because they expect the Windows values.

## Second-run fix (2026-11-28)
Closed the two remaining code-level causes on `release/1.0.0`:

1. **`leak_check` driver closure removed (`src/compiler/90.tools/leak_check/external_runner.spl`):**
   - Removed `use app.compile.native.{find_cpp_compiler}`,
     `use compiler.driver.driver_api_codegen_backends.{aot_c_file}`, and
     `use compiler.common.driver_compile_result.{CompileResult}`.
   - Kept `use std.io_runtime.{file_exists}` (with `env_get`, `platform_name`,
     and `use app.io.mod.{process_run}`) and added local `find_simple_binary()`
     + `find_cpp_compiler()` helpers so C++ generation runs out-of-process via
     `process_run(simple_bin, ["compile", cfg.source_file, "--emit-c", "-o", temp_cpp])`.
   - Zero `compiler.driver.*` or `app.compile.*` imports remain in `external_runner.spl`.

2. **Worker peak override no longer hides higher recorded peaks (`src/app/cli/shard_mem_clamp.spl`):**
   - Updated `shard_worker_estimate_kib_v1` so when `override_kb > 0` and
     `best > 0` (`worker_peaks_kib` has recorded peaks), it returns
     `shard_commit_estimate_kib_v1(override_kb, shard_measured_estimate_kib_v1(best))`
     (treating the override as a floor, matching `shard_commit_unmeasured_estimate_kib_v1`),
     while still returning `override_kb` when `best <= 0`.

### Tests & Verification (2026-11-28)
- Added `test/01_unit/compiler/tools/leak_check/external_runner_closure_isolation_spec.spl`.
- Updated `test/01_unit/app/cli/shard_peak_persistence_spec.spl`,
  `test/01_unit/app/cli/shard_commit_admission_spec.spl`, and
  `test/01_unit/compiler/driver/native_build_pool_memory_admission_spec.spl`.
- Verification scope on the Nov 16 Rust seed binary (`/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`):
  - Full `simple test` / `simple check` runs hit pre-existing seed parser failure
    `src/lib/common/types.spl:23:19: Unexpected token: expected As, found Newline`.
  - Isolated seed syntax probe passed with zero parse errors across all modified/new files.
  - Self-contained seed execution (`JIT` and `SIMPLE_EXECUTION_MODE=interpret`)
    verified `shard_worker_estimate_kib_v1` outputs `(1234, 4613734, 10000000, 32012040)`.
  - `sh scripts/audit/direct-env-runtime-guard.shs --working` passed (`STATUS: PASS`).
