# Linux aarch64 Cranelift Stage 2: `src/app/io/mod.spl` exceeds the per-file budget

- **Status:** OPEN performance/timeout issue; the automatic same-cache retry completed, so this was not the final Stage 2 admission failure.
- **Observed:** 2026-10-02, `release/1.0` plus draft PRs #2209 and #2227, `--backend=cranelift --jobs=20 --jobs-memory-policy=explicit-count`.

The first Stage 2 native-build compiled 1,132 modules and failed exactly one: `src/app/io/mod.spl` hit the seed's default 300-second per-file timeout under concurrent compilation. The bootstrap retried once with the same producer-scoped cache, reused 1,130 modules, rebuilt three, and linked the Stage 2 candidate. Its later `p2_add` sanity failed on a separate cold HIR inventory generation mismatch.

`COMPILER_BUILD_TIMEOUT_SECONDS=1800` bounded the post-build sanity probes and did not change the native-build per-file deadline. `SIMPLE_NATIVE_FILE_TIMEOUT` controls that deadline; it was unset in this run. Measure the module's isolated and concurrent compile time before choosing a larger bound or reducing its codegen cost. Preserve the cache on any retry.

Evidence: `/dev/shm/simple-release10-phase2-20261002/output/stage3/aarch64-unknown-linux-gnu/stage2-tmp/stage2-native-build.before-cache-retry.log` and `/dev/shm/simple-release10-phase2-20261002/logs/bootstrap-combined-f81ca6c-invalidate-stage2.log`.

## 2026-10-09 recurrence and retry eligibility correction

Release `3d7141f912c1047854090f8e068c4214f0c61031`, Linux aarch64,
Cranelift, 20 workers: `src/app/io/mod.spl` again exceeded 300 seconds.
The native coordinator then refused replacement admission, so the failure
report contained one timeout and 520 `NOT_ATTEMPTED` rows. The wrapper's
single-row retry predicate rejected this cascade and stopped before admission.

The retry predicate now accepts exactly one timeout plus only the exact
timeout-induced deferral reason. Both declared counts must match the failure
rows. A second timeout, unrelated failure/deferral, missing summary, or count
mismatch still rejects retry. The wrapper retains the existing limit of one
same-command retry and preserves the first log and RSS receipt. This fixes
retry eligibility; the underlying module compilation cost remains OPEN.

Failure evidence is preserved under
`/home/yoon/dev/simple-release-1.0-codex/build/native_probe/linux-arm-phase3-20261009/`:
`stage2-attempt1-native.log`, `stage2-attempt1-command.transcript`, and
`bootstrap-attempt1.log`. A separate operational retry uses the preserved cache,
20 workers, and `SIMPLE_NATIVE_FILE_TIMEOUT=1200`; it does not establish that
the performance issue is fixed.
