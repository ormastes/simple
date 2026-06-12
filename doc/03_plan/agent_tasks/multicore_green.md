# Multicore Green Parallel Agent Plan

Date: 2026-06-06

## Current State Snapshot

- Current cross-language Docker evidence is
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`.
- Large fanout stress currently shows Go ahead of Simple multicore green, while
  both stay ahead of the C pthread-per-task baseline:
  Go `6.533 ms`, Simple multicore green native `9.638 ms`, C pthreads
  `63.791 ms`.
- Fresh isolated 2026-06-11 evidence now shows the earlier `thread_spawn`
  native zero-join blocker is closed end to end: host-native public
  `thread_spawn`, `thread_spawn_with_args`, and the Docker profile OS-thread
  rows are all green with the rebuilt runtime plus the explicit Docker binary
  override fix in `scripts/check/check-cross-language-perf.shs`. Historical
  tracking remains in
  `doc/08_tracking/bug/thread_spawn_native_zero_join_2026-06-11.md`.
- Cooperative-green SMF mutable-global crash evidence is now closed by
  `test/03_system/feature/usage/cooperative_green_smf_mutable_global_regression_spec.spl`
  and the mirrored manual under `doc/06_spec`.
- The direct SMF function-valued global/global-array blocker in this lane is
  now closed. Historical tracking remains in
  `doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md`,
  and positive regression coverage now lives in
  `test/03_system/feature/usage/cooperative_green_smf_function_global_regression_spec.spl`.
- SimpleOS green-carrier hosted, live, and final AP ring/user handoff evidence
  is current in
  `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md`; the final
  handoff lane is closed by the opt-in
  `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1` marker triplet proof and
  remains separately gated so readiness markers cannot be mistaken for final
  hardware proof.
- Current source-built hosted-native fairness evidence is stricter than the
  checked-in `bin/release/simple` binary for this lane: the helper-return
  function-value probes, helper-side `Channel.id()` native path, the smaller
  pool-worker struct-send path, the function-valued local or parameter array
  path such as `val callbacks = [step_fn]`, inline lambda array literals such
  as `val callbacks = [\: 7]`, the function-value loop-return path, the direct
  by-value struct-array runtime shape, and the stale helper-side array-literal
  hybrid fallback are now fixed on rebuilt debug binaries. The later
  post-join array-return blocker is also closed: post-join `println` work
  before returning a local result array now prints `result=7` with `EXIT=0`
  in the regression spec and Docker-isolated rerun. This evidence remains
  perf-sensitive because the host native compile/run SSpecs take about
  60 seconds. The checked-in release binary remains tracked as stale evidence
  in `doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`.

## Coordination Contract

- Owned lane: multicore-green runtime-pool evidence, Go-thread research,
  profile scripts, and SimpleOS green-carrier scheduler evidence.
- Preserve public API names and semantics:
  `thread_spawn` is the explicit OS-thread API, `cooperative_green_spawn` is
  the primary current-carrier cooperative queue surface,
  `cooperative_green_spawn_value` remains the precomputed-result helper for
  callers that already have a value, and
  `multicore_green_spawn` is the current Pure Simple bounded-worker M:N
  candidate over `rt_pool_*`.
- Do not use numbered API names to distinguish behavior.
- Do not rewrite Simple features in C/Rust for benchmark wins. C, Go, and Rust
  are evidence baselines or seed/runtime implementation contexts only.
- Executable SPipe specs go under `test/`; generated/manual docs go under
  `doc/06_spec`; `doc/06_spec/**/*_spec.spl` must remain zero.
- Agents must not treat `thread_spawn_with_args` native timings as profile
  scheduler evidence. That ABI is covered by
  `scripts/check/check-thread-spawn-with-args-native.shs`; profile OS-thread
  rows stay on `thread_spawn`.

## Shared Inputs

- `doc/01_research/domain/multicore_green.md`
- `doc/01_research/lib/threading/go_vs_simple_threads.md`
- `doc/01_research/local/multicore_green.md`
- `doc/02_requirements/feature/multicore_green.md`
- `doc/02_requirements/nfr/multicore_green.md`
- `doc/04_architecture/runtime/multicore_green.md`
- `doc/05_design/multicore_green.md`
- `doc/03_plan/sys_test/multicore_green.md`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
- `scripts/check/check-cross-language-perf.shs`
- `src/lib/nogc_async_mut/concurrent/cooperative_green.spl`
- `src/lib/nogc_async_mut/concurrent/multicore_green.spl`
- `src/os/kernel/scheduler/green_carrier.spl`

## Go Profile Evidence Agent

Goal: keep the profile harness honest about Go-style M:N scheduling, C pthread
baselines, and Simple concurrency model labels.

Primary paths:

- `scripts/check/check-cross-language-perf.shs`
- `test/05_perf/profile_scripts/profile_report_contract_test.shs`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
- `doc/06_spec/test/05_perf/stress/multicore_green_cross_language_gate_spec.md`

Deliverables:

- cross-language report with separate rows for Simple OS threads, cooperative
  green, multicore green, C pthreads, Go goroutines, RSS, artifact footprint,
  and Simple-vs-Go-vs-C large fanout stress;
- numeric SPipe gate that rejects `fail`, `n/a`, and missing rows for required
  native evidence;
- report text that clearly says cooperative green is not Go M:N;
- reproducibility knobs in the report for worker counts and timeouts.

Acceptance evidence:

- `sh test/05_perf/profile_scripts/profile_report_contract_test.shs cross_language scripts/check/check-cross-language-perf.shs doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
- `bin/release/simple test test/05_perf/stress/multicore_green_cross_language_gate_spec.spl --mode=interpreter --clean`
- report row proving Go beats C pthreads in isolated large fanout stress with
  Go `GOMAXPROCS` pinned to `CPU_WORKERS`.
- report row showing Simple multicore green native still beats the C pthread
  large fanout stress baseline while remaining slower than Go until further
  scheduler/runtime work lands.

## Simple OS-Thread Baseline Agent

Goal: keep Simple's explicit OS-thread baseline working and distinct from green
thread claims.

Primary paths:

- `src/lib/nogc_sync_mut/concurrent/thread.spl`
- `src/lib/nogc_async_mut/concurrent/thread.spl`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `scripts/check/check-thread-spawn-with-args-native.shs`
- `doc/08_tracking/bug/native_thread_spawn_with_args_abi_2026-06-06.md`

Deliverables:

- passing fork-join coverage using `thread_spawn`;
- focused native smoke coverage for `thread_spawn_with_args`;
- documentation saying when a profile row uses OS threads vs runtime-pool
  logical tasks.

Acceptance evidence:

- `bin/release/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
- `sh scripts/check/check-thread-spawn-with-args-native.shs`

## Cooperative Green Semantics Agent

Goal: preserve and test cooperative green as a lightweight current-carrier
queue, not CPU-parallel M:N work.

Primary paths:

- `src/lib/nogc_async_mut/concurrent/green_thread.spl`
- `src/lib/nogc_async_mut/concurrent/cooperative_green.spl`
- `test/01_unit/lib/nogc_async_mut/cooperative_green_spec.spl`
- `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`
- `doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md`

Deliverables:

- current-carrier queue semantics with deterministic run-all behavior;
- profile-safe value scheduling path while function-valued native storage is
  blocked;
- explicit docs that cooperative green is not Go M:N.

Acceptance evidence:

- cooperative green unit/system specs pass;
- cross-language report keeps cooperative rows separate from M:N rows;
- blocker docs record the closed SMF/native runtime fixes and keep the
  green/cooperative SSpec runner mismatch regression-covered.

## Multicore Green Runtime-Pool Agent

Goal: make `multicore_green_spawn` the Simple M:N candidate only when runtime
pool use is proven.

Primary paths:

- `src/lib/nogc_async_mut/concurrent/multicore_green.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_spec.spl`
- `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
- `test/05_perf/stress/multicore_green_fanout_spec.spl`
- `doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md`

Deliverables:

- handle evidence methods remain stable:
  `used_runtime_pool()` and `ran_inline_fallback()`;
- profile workloads fail if a native M:N row would silently fall back inline;
- checksum parity with OS-thread and cooperative rows.

Acceptance evidence:

- `bin/release/simple check test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
- native build/run of `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
  exits `0`, proving every handle reported `used_runtime_pool()`;
- `bin/release/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
- cross-language report contains `used_runtime_pool()` evidence text.

## Host Fairness And Blocking Agent

Goal: keep the remaining host-side Go-parity gap explicit and move it toward
real closure rather than letting SimpleOS-only scheduler evidence overclaim the
host runtime lane.

Primary paths:

- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`
- `test/03_system/feature/usage/multicore_green_host_parity_gap_spec.spl`
- `doc/01_research/lib/threading/go_vs_simple_threads.md`
- `doc/04_architecture/runtime/multicore_green.md`
- `doc/05_design/multicore_green.md`

Deliverables:

- dedicated tracking for the remaining hosted multicore-green parity gap;
- executable proof that hosted blocking compensation stays fixed while
  fairness/preemption remains open until stronger evidence lands;
- executable blocker coverage for the explicit resumable host-fairness path,
  including the scalar-state `multicore_green_spawn_sliced` source/native
  regression and historical closure of the earlier callback-id prototype;
- updated research and architecture text when that boundary changes.

Acceptance evidence:

- `bin/release/simple test test/03_system/feature/usage/multicore_green_host_parity_gap_spec.spl --mode=interpreter --clean`
- `bin/release/simple test test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl --mode=interpreter --clean`
- `bin/release/simple test test/03_system/feature/usage/multicore_green_tracking_spec.spl --mode=interpreter --clean`
- `bin/release/simple lint doc/08_tracking/feature/feature_db.sdn`

## SimpleOS Green Carrier Agent

Goal: keep SimpleOS support aligned with the host/library API split while
progressing toward scheduler-aware multicore green execution.

Primary paths:

- `src/os/kernel/scheduler/green_worker.spl`
- `src/os/kernel/scheduler/green_task.spl`
- `src/os/kernel/scheduler/green_carrier.spl`
- `src/os/kernel/scheduler/scheduler.spl`
- `examples/09_embedded/simple_os/arch/x86_64/green_carrier_probe_entry.spl`
- `test/03_system/os/simpleos/feature/*green*_spec.spl`
- `test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl`

Deliverables:

- hosted SimpleOS cooperative/multicore/channel-wake contracts;
- hosted SimpleOS cooperative/multicore specs are trusted current evidence
  again because the green/cooperative SSpec runner mismatch is closed and
  regression-covered;
- live QEMU proof for AP startup plus scheduler-visible CPU1 green dispatch;
- final hardware context-switch handoff kept separate from scheduler-state
  proof and backed by the `HW_HANDOFF_PASS`, `USER_ENTRY_PASS`, and
  `USER_SYSCALL_PASS` marker triplet.

Acceptance evidence:

- hosted SimpleOS green specs pass in interpreter mode after the
  `doc/08_tracking/bug/green_thread_spec_runner_mismatch_2026-06-11.md`
  blocker is closed and regression coverage is in place;
- `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean`
- `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 bin/release/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean`
  proves the final AP ring/user handoff marker triplet.

## Merge Sequencing

1. Go Profile Evidence Agent owns profile/report contract changes before any
   performance claim.
2. Simple OS-Thread Baseline Agent fixes or tracks OS-thread API blockers
   before profile rows consume those APIs.
3. Cooperative Green Semantics Agent and Multicore Green Runtime-Pool Agent can
   run in parallel because cooperative green and multicore green must stay
   semantically distinct.
4. Host Fairness And Blocking Agent keeps the remaining host-side Go-parity
   gap explicit while stronger runtime evidence is still missing.
5. SimpleOS Green Carrier Agent consumes stable host/library contracts into
   SimpleOS and QEMU proof.
6. Generated manuals and `doc/09_report` are refreshed after executable specs
   and profile scripts change.

## Conflict Rules

- If a change touches `scripts/check/check-cross-language-perf.shs`, Go Profile
  Evidence Agent owns the report shape and must rerun the profile contract.
- If a change touches `thread_spawn_with_args`, Simple OS-Thread Baseline Agent
  must update `scripts/check/check-thread-spawn-with-args-native.shs` and the
  matching tracking note.
- If a change claims Go-like M:N behavior, Multicore Green Runtime-Pool Agent
  must provide `used_runtime_pool()` evidence and Go Profile Evidence Agent must
  gate the row numerically.
- If a change claims hosted fairness/preemption parity with Go, Host Fairness
  And Blocking Agent must update the dedicated host-gap tracker and executable
  parity-gap spec before the lane can be described as closed.
- If a SimpleOS QEMU probe uses a fixed-slot helper, SimpleOS Green Carrier
  Agent must state exactly what is proven and what remains future hardware
  handoff work.

## Required Handoff Commands

Each agent reports:

- `git status --short -- <owned paths>`
- focused `simple check` and `simple test` commands run;
- profile command and `doc/09_report` path when profile rows change;
- optimizer output for touched `.spl` files;
- `find doc/06_spec -name '*_spec.spl' | wc -l`
- unresolved blockers or files intentionally left untouched.

## Current Sync Status (2026-06-12)

- This refresh follows the pushed thread-spawn native regression sync
  (`test: keep thread spawn native regression green`) and records the current
  multicore-green lane evidence after rebasing onto the latest `origin/main`.
- Focused current-source checks on 2026-06-12 passed for the thread-spawn
  native regression, multicore-green helper handles, resumable-stepper blocker
  boundary, worker callback registry, channel struct send, callable field,
  fairness/preemption gap docs, thread-yield gap docs, blocking compensation,
  parallelism bound, host parity tracking, native function-value loop return,
  native function-value param-array, native struct-array, hosted SimpleOS
  cooperative green, hosted SimpleOS multicore green, hosted SimpleOS green
  channel wake, profile report contract, and cross-language gate.
- The multicore-green lane has also synced:
  - Docker auto-binary selection preferring `bin/simple` / `bin/release/simple`
    while leaving `src/compiler_rust/target/debug/simple` as an explicit
    regression override;
  - the fixed generated `fanout_stress_multicore_green.spl` source shape;
  - refreshed Go-vs-Simple research and SimpleOS evidence docs;
  - closure-aligned architecture, design, tracker, and report text for the
    final SimpleOS AP ring/user handoff lane;
  - handle-array native lowering and thread-spawn native regression coverage.
- The shared workspace remains dirty outside this lane because other sessions
  are active in the checkout; future multicore-green syncs must keep unrelated
  files out of lane commits unless the user explicitly asks for an integration
  commit.
