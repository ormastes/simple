# `build_cache_persist` is a non-atomic whole-file rewrite — prerequisite for parallel native-build step 5

- **ID:** build_cache_persist_non_atomic_rewrite_blocks_parallel_step5_2026-11-09
- **Status:** OPEN
- **Severity:** medium (latent torn manifest on crash today; hard blocker for concurrent publishers)
- **Blocks:** `native_build_step5_serial_threads_ignored_2026-09-04` (filed as its named prerequisite, per owner decision 2026-11-09)

## Defect

`build_cache_persist` (`src/compiler/80.driver/driver_build/incremental.spl`,
`pub fn build_cache_persist`) renders every entry and writes `cache.cache_path`
directly with `incremental_file_write_text` — no temp file + atomic rename, no
merge with entries another process published. `driver_native_collect_capsule_result_v1`
(`driver_aot_native_output.spl`) calls it once per module.

Consequences:
1. **Today, concurrency 1:** a crash/kill mid-write leaves a torn manifest; the
   next run's phase-1 cache lookup (manifest-driven, not receipt-driven) loses
   every hit.
2. **Any concurrent publisher** (the planned `build_parallel()` step-5 route)
   races last-writer-wins and drops sibling entries — so parallel step 5 would
   yield objects with zero parent cache hits.

## Required (prerequisite contract)

- Write to `<cache_path>.tmp.<pid>` then atomic rename over `cache_path`.
- Concurrent publishers either write per-worker manifest fragments merged by the
  parent, or re-read + merge under the rename (lockless, per lockless-by-default).
- Spec: a red test that persists two caches from two writers and asserts both
  entry sets survive; and a truncated-write test asserting the old manifest
  stays loadable.

Second named prerequisite (already in the parent record): phase-1 hits require a
manifest entry, so worker fragments must be merged before the parent looks up.
