# native-build cache is all-or-nothing: a timeout writes NOTHING, so reruns are always cold

- **Date:** 2026-07-26
- **Lane:** `native-build --cache-dir` (both backends; observed on SimpleOS WM harness kernel builds)
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Symptom
SimpleOS WM harness runs 5-7 each burned 2h+ compiling the kernel closure and timed
out; every run started fully cold. After 2h, the passed `--cache-dir` directory was
**completely empty** (0 bytes) — not even a subdirectory.

## Root cause (two stacked all-or-nothing layers)
1. **Cache writes are unreachable until codegen starts.** `--cache-dir` is honored
   (parsed in `src/app/io/_CliCompile/compile_targets.spl:861-870`, exported as
   `SIMPLE_NATIVE_BUILD_CACHE_DIR`, consumed in
   `src/compiler/80.driver/driver_aot_output.spl:118`), but every write — even the
   cache-scope `rt_dir_create` (`driver_aot_output.spl:336`) — happens inside
   `compile_to_native()`. The worker must first finish frontend parsing + import
   resolution + MIR construction for the WHOLE `--entry-closure` graph. The observed
   timeouts fire during that pre-codegen phase, so codegen — and thus any cache
   write — never begins. An empty cache dir is the signature of "died in frontend".
2. **The cache index is saved exactly once, at the very end.** Per-module `.o` files
   are written progressively (`driver_aot_output.spl:406-440`) but
   `build_cache.save()` runs only after ALL modules compile
   (`driver_aot_output.spl:465`). A kill mid-codegen leaves orphan `.o` files with no
   `build_cache.sdn`, so the next run misses on every module anyway.

Also verified: NO target/mode guard disables caching for
`--target x86_64-unknown-none` / `--mode dynload` — caching would work if reached.
The hard subprocess kill (`process_run_timeout`, no SIGTERM grace) leaves no chance
to flush. Conclusion: **under the current code, run N+1 after a timeout can never be
warm** — the observed repeated cold 2h runs are predicted behavior, not bad luck.

## Where the 2h actually goes
The 3 known giant-literal files (>60s each; `backend_vulkan_spirv_raster_blobs.spl`
211KB, `backend_vulkan_font_spirv.spl` 65KB, plus the since-shrunk HTML layout
renderer) are in the WM entry closure but only account for minutes. The bulk is the
frontend/MIR pass over the full compositor/engine2d/vulkan graph — invisible today
(see `simpleos_harness_silent_native_build_2026-07-26.md`; mitigation
`SIMPLE_COMPILER_TRACE=1`).

## Fix set (described, not yet applied)
1. **Incremental index persistence:** batched `build_cache.save()` every N modules in
   the Phase-2 loop instead of the single save at `:465`.
2. **Early on-disk phase marker** so a killed run records whether it died in frontend
   vs codegen (currently zero signal).
3. **Two-stage SIGTERM→SIGKILL** in `process_run_timeout` usage so the driver can
   flush the cache index on a soft deadline.
4. **Frontend cost itself:** lazily load / externalize the SPIR-V byte-literal blobs;
   longer term, cache or parallelize the frontend/MIR pass for large closures.

## Non-finding
`build_native_from_cache()` (`src/compiler/70.backend/build_native.spl:44`) is dead
code — exported, never called; ignore it when fixing.

## Fix status (2026-07-26, same day)
Items 1-3 implemented and seed-lane-verified: incremental `build_cache.save()`
every 5 modules via `_compile_one_module_and_cache` (kill mid-Phase-2 leaves a
valid populated index), per-line `rt_stdout_flush()` after `[NATIVE]` prints
(log grows live under redirects), `phase.marker` written at cache-scope creation,
and `--kill-after` grace 5s→10s. Correction to the original analysis: the kill
was already two-stage (`timeout --kill-after`), not hard — but no SIGTERM handler
exists, so incremental persistence (not grace) is the effective fix. NOTE: takes
effect on the deployed lane only after the next stage4 redeploy.

## Related quirk found during verification
On the SEED lane, `native_build_compiler_identity()` fell back to
`uncacheable-{pid}-{timestamp}` (`driver_build/incremental.spl:120`), making every
seed invocation its own cache scope — seed-lane reruns can never warm regardless
of the fixes above. The deployed-binary lane hashes `argv[0]` and should scope
stably; if a harness cache stays cold after redeploy, check this identity path
first.
