# Feature: fat32-4k-overwrite-c-baseline-gap

## Raw Request
Redirect: do not work on `c_runtime_exclusion_analysis`; that older task already completed. Instead, use the repo's $sp_dev workflow for `fat32_4k_overwrite_c_baseline_gap`. Work in your forked workspace only and do not push. You are not alone in the codebase: do not revert edits made by others; keep your write scope to FAT32/storage files, the assigned tracker entry, and `.spipe/<slug>/state.md`. Locate the exact open entry, define acceptance criteria, fix or close with evidence, run focused tests, and final with: status, changed paths, tests run, and blockers.

## Task Type
bug

## Refined Goal
Resolve the remaining FAT32 4K overwrite C baseline tracker by verifying the direct-C performance gate and either collecting VFAT same-device evidence or documenting the exact host blocker that prevents it.

## Acceptance Criteria
- AC-1: The tracker entry `doc/08_tracking/bug/fat32_4k_overwrite_c_baseline_gap_2026-05-28.md` identifies whether the remaining gap is closed or externally blocked.
- AC-2: `SIMPLE_LIB=src bin/simple check test/05_perf/bench/fat32_4k_compare.spl` passes.
- AC-3: `FAT32_4K_RUNS=3 scripts/perf/run-fat32-4k-cfat-baseline.shs` passes the repeated direct-C comparison.
- AC-4: VFAT readiness is verified with `scripts/perf/prepare-fat32-4k-vfat.shs --diagnose` and, when unavailable, the tracker records the concrete missing privilege or mount condition.
- AC-5: The required-VFAT gate either passes with recorded median p50 values or fails cleanly before benchmarking with readiness evidence.

## Scope Exclusions
No broad runtime ABI changes, no new unsafe byte-array externs, no non-FAT32 source edits, no mount/remount operations requiring interactive privilege, and no pushes.

## Phase
ship-done

## Log
- dev: Created state file with 5 acceptance criteria (type: bug).
- verify: `SIMPLE_LIB=src bin/simple check test/05_perf/bench/fat32_4k_compare.spl` passed.
- verify: `FAT32_4K_RUNS=3 scripts/perf/run-fat32-4k-cfat-baseline.shs` passed with Simple median p50 25us/31us vs direct C 32us/39us.
- verify: `scripts/perf/prepare-fat32-4k-vfat.shs --diagnose` reported existing `/tmp/simple_vfat_bench_mnt` as vfat but not writable and unseeded; noninteractive sudo unavailable.
- verify: `FAT32_4K_RUNS=1 REQUIRE_VFAT_BASELINE=1 scripts/perf/run-fat32-4k-cfat-baseline.shs` failed cleanly before benchmarking because VFAT is missing/unseeded/unwritable.
- ship: Closed tracker with direct-C evidence and an external VFAT mount blocker.
