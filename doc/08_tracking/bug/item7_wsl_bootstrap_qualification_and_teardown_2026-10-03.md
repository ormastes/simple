# Item 7: bounded WSL bootstrap did not produce a qualified runtime

- **Filed:** 2026-10-03
- **Status:** OPEN / runtime acceptance BLOCKED; three bootstrap attempts exhausted.
- **Frozen source:** `109c401782091a6b20f3bc4ed70adc79da272865`.
- **Workspace:** Ubuntu WSL, `/root/simple-item7-qualified-20261003` (isolated ext4 checkout).
- **Impact:** No Stage 2 executable, full CLI, or test runner was admitted. Item 7 executable acceptance and RED/GREEN evidence remain **NOT RUN**. Later integration commits are not covered by this source snapshot. No release readiness or merge is justified by this run.

## Observed attempts

1. LLVM bootstrap exited 1 at provider admission. `/opt/toolchains/LLVM-23.1.2-Linux-X64/bin/llvm-config --version` reports `23.1.2`, but `--shared-mode` reports `static`; the installation has no `libLLVM.so` provider. The only inspected system shared provider is LLVM 21. Repository admission correctly rejected it. Existing apt metadata listed runtime packages through LLVM 22, not 23. No provider gate was weakened.
2. Cranelift bootstrap exited 1 during fingerprinting: `cannot canonicalize llvm-config '/usr/bin/llvm-config'`. That path is a symlink chain. The existing `prepare-simpleos-ci-host.shs` documents binding the physical executable; the third attempt used that supported environment correction.
3. Cranelift with physical `LLVM_CONFIG` completed all four Rust authority builds and canonical preflight (`5 check(s) run, 0 failed, 0 skipped`). Cargo authority preparation took 1088 seconds; preflight took 178 seconds. Stage 2 compilation remained active until the outer bounded launch ended, without producing its executable. This proves bootstrap preparation, not Simple acceptance.

The third command, from the frozen checkout, was:

```sh
timeout --kill-after=30s 2400s env SIMPLE_NO_STUB_FALLBACK=1 \
  LLVM_CONFIG=/opt/toolchains/LLVM-23.1.2-Linux-X64/bin/llvm-config \
  BOOTSTRAP_VERIFY_TIMEOUT_SECONDS=900 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --full-bootstrap --stop-after-stage2 --backend=cranelift \
  --jobs=4 --keep-going --output=build/bootstrap/item7-qualified-cranelift-20261003
```

## Terminal and containment evidence

The tool launcher returned **exit 1**, not a recorded exit 124. The progress watcher recorded orchestrator PID 26752 as `terminal=exited` at elapsed 2442 seconds. The native child PID 57223 nevertheless remained active under RSS watchdog PID 57214 in its own session/process group 57223. Thus controller termination did **not** establish child quiescence.

After verifying the orphan's command and private runtime/cache paths, the agent sent `SIGTERM` only to process group 57223. The compiler and watchdog then disappeared; the RSS receipt reported `quiescent=1`. The intended `stage2/x86_64-unknown-linux-gnu/simple` file was absent. This is a teardown defect and incomplete compilation evidence, not a diagnosed collection implementation failure.

## Retained evidence and next action

All paths below are relative to the frozen workspace; no cache was deleted:

- `build/native_probe/item7-bootstrap-20261003.log`
- `build/native_probe/item7-bootstrap-cranelift-20261003.log`
- `build/native_probe/item7-bootstrap-cranelift-physical-config-20261003.log`
- `build/bootstrap/item7-qualified-cranelift-20261003/bootstrap-progress.log`
- `build/bootstrap/item7-qualified-cranelift-20261003/logs/x86_64-unknown-linux-gnu/stage2-native-build.log` and `.rss.env`
- `build/bootstrap/item7-qualified-cranelift-20261003/stage3/x86_64-unknown-linux-gnu/stage2-native-cache` (frontend/HIR/native state; reuse counts not established).

Repair and test controller-to-watchdog cancellation before another bounded build. Preserve and validate the cached lineage against the next explicit source freeze. Supply a genuinely admitted LLVM 23 shared provider for the mandatory LLVM scenarios. Do not substitute Rust-seed execution, a compile-only binary, or Cranelift results for qualified interpreter/LLVM acceptance. No fourth attempt was started.

## Focused cancellation repair (no bootstrap rerun)

The POSIX watchdog now pins its launching parent PID and detects reparenting.
Loss of a controller cancels a live workload through the existing TERM/grace
and verified quiescence path, with `status=controller-exited` and exit 143.
An already completed workload keeps its original result. The Windows Job
Object path is unchanged; this focused evidence is from Ubuntu WSL.

Actual RED: `process_tree_rss_controller_exit_test.shs` exited 1 in 8.9 seconds
before the repair: `controller exited but watchdog left workload running without a receipt`.
The test cleaned up its disposable processes.

Actual GREEN after the repair: the same regression passed three real process
cases in 5.1 seconds: killing only the controller stops an isolated shell and
sleep child; a live controller permits normal completion; pausing observation,
letting the workload finish, then killing the controller preserves exit 0.
The existing `process_tree_rss_deadline_test.shs` also passed its sampling,
timeout/grace, hung-sampler and cold-admission cases once. Perl syntax and
`git diff --check` passed. No previously green execution was repeated.

This repairs the demonstrated POSIX cancellation gap. It does not qualify a
compiler, establish feature RED/GREEN, remove the missing LLVM provider, or
authorize a release merge. Bootstrap and item 7 runtime acceptance remain pending.
The repaired helper exists only in the acceptance worktree/commit; it was not
copied into the frozen `109c4017820` bootstrap workspace. That workspace retains
its original helper and source lineage. No new bootstrap was performed.
