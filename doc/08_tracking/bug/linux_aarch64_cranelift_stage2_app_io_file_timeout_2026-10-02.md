# Linux aarch64 Cranelift Stage 2: `src/app/io/mod.spl` exceeds the per-file budget

- **Status:** OPEN performance/timeout issue; the automatic same-cache retry completed, so this was not the final Stage 2 admission failure.
- **Observed:** 2026-10-02, `release/1.0` plus draft PRs #2209 and #2227, `--backend=cranelift --jobs=20 --jobs-memory-policy=explicit-count`.

The first Stage 2 native-build compiled 1,132 modules and failed exactly one: `src/app/io/mod.spl` hit the seed's default 300-second per-file timeout under concurrent compilation. The bootstrap retried once with the same producer-scoped cache, reused 1,130 modules, rebuilt three, and linked the Stage 2 candidate. Its later `p2_add` sanity failed on a separate cold HIR inventory generation mismatch.

`COMPILER_BUILD_TIMEOUT_SECONDS=1800` bounded the post-build sanity probes and did not change the native-build per-file deadline. `SIMPLE_NATIVE_FILE_TIMEOUT` controls that deadline; it was unset in this run. Measure the module's isolated and concurrent compile time before choosing a larger bound or reducing its codegen cost. Preserve the cache on any retry.

Evidence: `/dev/shm/simple-release10-phase2-20261002/output/stage3/aarch64-unknown-linux-gnu/stage2-tmp/stage2-native-build.before-cache-retry.log` and `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-combined-f81ca6c-invalidate-stage2.log`.
