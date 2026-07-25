# Multicore Green Parallel Agent Plan

Date: 2026-06-14

## Current State Snapshot

- Current cross-language Docker evidence is
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`.
- Large fanout stress currently shows Go ahead of Simple multicore green, while
  both stay ahead of the C pthread-per-task baseline:
  Go `6.533 ms`, Simple multicore green native `9.638 ms`, C pthreads
  `63.791 ms`.
- Hosted CPU-heavy fairness now has two explicit evidence paths:
  `multicore_green_spawn_sliced` for scalar-state requeueing and ordinary
  `multicore_green_spawn` loop-body safepoints for compiler-inserted
  runtime-pool polling. Broader non-loop/native-call preemption remains outside
  the current claim.
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
  checked-in `bin/release/simple` binary for this lane. Helper-return probes,
  function-value loop-return, struct-array/runtime, and post-join array-return
  regressions have focused current-source coverage. The release wrapper remains
  probe-required deploy-artifact evidence in
  `doc/08_tracking/bug/multicore_green_release_binary_stale_2026-06-11.md`:
  `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` materializes the
  ignored platform delegate, and profile/user wrappers must skip stale
  delegates unless they pass `--version`.
  These native compile/run SSpecs remain perf-sensitive at roughly one minute.
- 2026-06-14 fresh compiler evidence fixed the hosted native `rt_pool_join`
  value boundary without corrupting regular public `handle.join()` values:
  LLVM native-build tags raw runtime-pool join integers before storing them in
  Simple vregs, and Cranelift tags that result only for the native-project
  build lane where escaped closure returns are raw. Regular interpreter and
  `compile --native` paths leave `rt_pool_join` unchanged because the pool
  result is already a Simple value there. The public concurrency API contract
  and `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl` both pass,
  so the regular public facade and native-project runtime-pool smoke now agree
  on visible `handle.join()` semantics.

## Coordination Contract

- Owned lane: multicore-green runtime-pool evidence, Go-thread research,
  profile scripts, and SimpleOS green-carrier scheduler evidence.
- Preserve public API names and semantics:
  `thread_spawn` is the explicit OS-thread API, `cooperative_green_spawn` is
  the primary current-carrier cooperative queue surface,
  `cooperative_green_spawn_value` remains the precomputed-result helper for
  callers that already have a value, and
  `multicore_green_spawn` is the current Pure Simple bounded-worker M:N
  candidate over `rt_pool_*`. `multicore_green_spawn_sliced` is the explicit
  scalar-state fairness API for long Pure Simple work; the public API contract
  must keep the run/join marker `public_multicore_green_sliced_result=19 used_runtime_pool=true`.
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
- `test/05_perf/profile_scripts/profile_binary_autoselect_test.shs`
- `test/05_perf/profile_scripts/profile_docker_isolation_contract_test.shs`
- `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`
- `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`
- `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
- `doc/06_spec/05_perf/stress/multicore_green_cross_language_gate_spec.md`

Deliverables:

- cross-language report with separate rows for Simple OS threads, cooperative
  green, multicore green, C pthreads, Go goroutines, RSS, artifact footprint,
  ordinary large fanout, Simple-vs-Go-vs-C large fanout stress, and hosted
  sliced-fairness evidence;
- numeric SPipe gate that rejects `fail`, `n/a`, and missing rows for required
  native evidence;
- report text that clearly says cooperative green is not Go M:N;
- Docker isolation contract evidence proving crash-prone native, SMF, C, and Go
  profile runs stay behind a separate process/container boundary while reusing
  the canonical profile script;
- reproducibility knobs in the report for worker counts and timeouts.

Acceptance evidence:

- `sh test/05_perf/profile_scripts/profile_report_contract_test.shs`
- `sh test/05_perf/profile_scripts/profile_help_contract_test.shs`
- `sh test/05_perf/profile_scripts/profile_binary_autoselect_test.shs`
- `sh test/05_perf/profile_scripts/profile_docker_isolation_contract_test.shs`
- `sh test/05_perf/profile_scripts/concurrency_api_contract_test.shs`
- `src/compiler_rust/target/debug/simple run build/cross_lang_perf/hosted_sliced_fairness.spl --mode=interpreter`
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_cross_language_gate_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_large_profile_gate_spec.spl --mode=interpreter --clean`
- report rows proving Go fanout and Go stress fanout both beat C pthreads with
  Go `GOMAXPROCS` pinned to `CPU_WORKERS`.
- domain research refreshed against official Go docs on 2026-06-14, including
  Go 1.25 container-aware `GOMAXPROCS` and the Linux `containermaxprocs`
  GODEBUG setting, while keeping release profile evidence pinned to
  `GOMAXPROCS=$CPU_WORKERS`.
- no-arg profile contract output includes
  `report_index_checked=doc/09_report/README.md` and
  `agent_task_plan_checked=doc/03_plan/agent_tasks/multicore_green.md`,
  proving the current report index and agent handoff point at the same
  canonical freshbin evidence as the profile gate.
- report row showing Simple multicore green native still beats the C pthread
  large fanout stress baseline while remaining slower than Go until further
  scheduler/runtime work lands.
- 2026-06-14 native resolver evidence: `cargo test -p simple-compiler
  elf_utils::tests::resolves_runtime_pool_symbols` and
  `SIMPLE_BIN=src/compiler_rust/target/debug/simple sh
  test/05_perf/profile_scripts/concurrency_api_contract_test.shs` pass with
  `public_multicore_green_sliced_result=19 used_runtime_pool=true` and runtime-pool counter symbols
  exported by the rebuilt driver.

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

- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
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
- public pool counters remain stable:
  `multicore_green_submitted_count()`, `multicore_green_completed_count()`,
  `multicore_green_pending_count()`, `multicore_green_busy_count()`, and
  `multicore_green_blocked_count()`;
- profile workloads fail if a native M:N row would silently fall back inline;
- profile workloads print counter deltas and fail unless submitted/completed
  deltas match the runtime-pool handle count and pending/busy/blocked drain to
  zero after join;
- checksum parity with OS-thread and cooperative rows.

Acceptance evidence:

- `src/compiler_rust/target/debug/simple check test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
- native build/run of `test/01_unit/lib/nogc_async_mut/multicore_green_native.spl`
  exits `0`, proving every handle reported `used_runtime_pool()` and public
  submitted/completed/pending/busy/blocked counter evidence is consistent
  after join;
- `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
- cross-language report contains `used_runtime_pool()` evidence text plus
  `counter_delta=<submitted>/<completed>,pending=0,busy=0,blocked=0` evidence.

## Host Fairness And Blocking Agent

Goal: keep the host-side fairness boundary explicit: the supported CPU-heavy
host fairness contract includes `multicore_green_spawn_sliced` for explicit
scalar-state slicing and ordinary loop-body fairness through compiler-inserted
runtime-pool safepoints in `multicore_green_spawn` closures.

Primary paths:

- `doc/08_tracking/bug/host_multicore_green_fairness_preemption_gap_2026-06-11.md`
- `test/03_system/feature/usage/multicore_green_host_parity_gap_spec.spl`
- `doc/01_research/lib/threading/go_vs_simple_threads.md`
- `doc/04_architecture/runtime/multicore_green.md`
- `doc/05_design/multicore_green.md`

Deliverables:

- dedicated tracking for the hosted fairness decision and the remaining
  non-loop/native-call preemption boundary;
- executable proof that hosted blocking compensation stays fixed while sliced
  fairness and ordinary loop-body safepoints are the supported CPU-heavy fairness
  contracts;
- executable blocker coverage for the explicit resumable host-fairness path,
  including the scalar-state `multicore_green_spawn_sliced` source/native
  regression and historical closure of the earlier callback-id prototype;
- profile/report visibility for generated hosted sliced-fairness and
  loop-safepoint evidence, with source rows labeled as interpreter-inline
  semantic checks and native rows requiring `used_runtime_pool=true`;
- public API contract visibility for the scalar-state sliced API through
  `public_multicore_green_sliced_result=19 used_runtime_pool=true`;
- updated research and architecture text when that boundary changes.

Acceptance evidence:

- `src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_host_parity_gap_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_fairness_preemption_gap_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_thread_yield_gap_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_sliced_fairness_regression_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple test test/03_system/feature/usage/multicore_green_tracking_spec.spl --mode=interpreter --clean`
- `src/compiler_rust/target/debug/simple lint doc/08_tracking/feature/feature_db.sdn`

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
- hosted SimpleOS multicore evidence keeps the model/live boundary executable:
  the hosted spec has 7 scenarios and rejects stale wording that treats
  live AP or final ring/user proof as unavailable;
- live QEMU proof for AP startup plus scheduler-visible CPU1 green dispatch,
  with the scheduler-only lane rejecting final hardware handoff markers;
- final hardware context-switch handoff kept separate from scheduler-state
  proof and backed by the `HW_HANDOFF_PASS`, `USER_ENTRY_PASS`, and
  `USER_SYSCALL_PASS` marker triplet.

Acceptance evidence:

- hosted SimpleOS green specs pass in interpreter mode after the
  `doc/08_tracking/bug/green_thread_spec_runner_mismatch_2026-06-11.md`
  blocker is closed and regression coverage is in place;
- `SIMPLEOS_GREEN_CARRIER_QEMU_LIVE=1 src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean`
  proves readiness markers and must not emit `HW_HANDOFF_PASS=true`,
  `USER_ENTRY_PASS=true`, or `USER_SYSCALL_PASS=true`;
- `SIMPLEOS_GREEN_CARRIER_QEMU_HW_HANDOFF_LIVE=1 src/compiler_rust/target/debug/simple test test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl --mode=interpreter --clean`
  proves the final AP ring/user handoff marker triplet.

## Merge Sequencing

Profile shape gate: Go Profile Evidence Agent owns profile/report contract
changes before any performance claim.

OS-thread baseline gate: Simple OS-Thread Baseline Agent fixes or tracks
OS-thread API blockers before profile rows consume those APIs.

Green-semantics split gate: Cooperative Green Semantics Agent and Multicore
Green Runtime-Pool Agent can run in parallel because cooperative green and
multicore green must stay semantically distinct.

Host fairness gate: Host Fairness And Blocking Agent keeps sliced fairness,
ordinary loop-body safepoints, and the remaining non-loop/native-call boundary
explicit.

SimpleOS carrier gate: SimpleOS Green Carrier Agent consumes stable
host/library contracts into SimpleOS and QEMU proof.

Manual/report refresh gate: generated manuals and `doc/09_report` are
refreshed after executable specs and profile scripts change.

## Conflict Rules

- If a change touches `scripts/check/check-cross-language-perf.shs`, Go Profile
  Evidence Agent owns the report shape and must rerun the profile contract.
- If a change touches `thread_spawn_with_args`, Simple OS-Thread Baseline Agent
  must update `scripts/check/check-thread-spawn-with-args-native.shs` and the
  matching tracking note.
- If a change claims Go-like M:N behavior, Multicore Green Runtime-Pool Agent
  must provide `used_runtime_pool()` plus public counter-delta evidence, and Go
  Profile Evidence Agent must gate the row numerically.
- If a change claims hosted fairness/preemption parity with Go, Host Fairness
  And Blocking Agent must distinguish explicit sliced fairness, compiler-inserted
  ordinary loop-body safepoints, and any still-unproven non-loop/native-call
  preemption before the claim is accepted.
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

## Current Sync Status (2026-06-13)

- Current multicore-green lane state is rebased on the latest shared mainline
  and uses small jj slices for doc/spec/evidence refreshes so other-agent work
  remains separate.
- Recheck after syncing the scratch jj workspace to `a61
  perf(gui): escape html window text in one pass` passed the checked-in
  cross-language evidence gates:
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`,
  `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`, and
  `test/05_perf/stress/multicore_green_fanout_spec.spl`.
- The same recheck reran hosted SimpleOS green evidence without the opt-in QEMU
  live lane: `simpleos_cooperative_green_spec.spl`,
  `simpleos_multicore_green_spec.spl`, `simpleos_green_channel_wake_spec.spl`,
  and `simpleos_green_hardware_handoff_blocker_spec.spl` all passed.
- The latest docs/spec slice made `test/05_perf/README.md` point at every
  active profile-script gate for this lane: the canonical profile report
  contract, negative mutation contract, binary auto-selection regression,
  Docker isolation contract, concurrency API misuse contract, and
  `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`.
- Follow-up slices aligned the agent plan, architecture, design, and
  `.codex/skills/coding/SKILL.md` with the same concurrency API contract gate,
  and refreshed the architecture evidence path to
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`.
- The report index now promotes
  `doc/09_report/cross_language_perf_2026-06-11_thread_fix_refresh_freshbin.md`
  as current evidence and keeps the older Docker contract report historical.
- The tracking SSpec and generated manual now assert that the README keeps the
  large Go fanout, Simple multicore-green runtime-pool evidence,
  `queue_model=work_stealing`, and numeric-suffix API-alias rejection visible.
- The NFR verification gates now include
  `test/05_perf/profile_scripts/concurrency_api_contract_test.shs`, so
  numeric-suffix API-alias rejection and active source/profile scans are part
  of the selected non-functional gate rather than only tracking commentary.
- Focused checks from the latest pushed slice passed:
  - `src/compiler_rust/target/debug/simple native-build --clean --source src/lib --entry test/01_unit/lib/nogc_async_mut/multicore_green_native.spl --output build/test/multicore_green_native && ./build/test/multicore_green_native`
  - `sh scripts/check/check-thread-spawn-with-args-native.shs`
  - `src/compiler_rust/target/debug/simple test test/05_perf/stress/multicore_green_fanout_spec.spl --mode=interpreter --clean`
  - `test/03_system/feature/usage/multicore_green_tracking_spec.spl`
  - `test/05_perf/stress/multicore_green_large_profile_gate_spec.spl`
  - `test/05_perf/profile_scripts/profile_report_contract_test.shs`
  - `test/05_perf/profile_scripts/profile_report_contract_negative_test.shs`
  - `test/05_perf/profile_scripts/concurrency_api_contract_test.shs`
  - `doc/08_tracking/feature/feature_db.sdn` lint
  - `/sp_dev` wiring check through
    `sh scripts/setup/install-spipe-dev-command.shs --check`; the delegated
    submodule-gitlink check now has a read-only jj-workspace path, so the
    scratch pherallel lane can run it without a `.git` directory while repair
    still requires a Git index.
  - `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- Prior 2026-06-12/early-2026-06-13 evidence remains valid for Docker
  auto-binary selection, Docker isolation, the fixed generated
  `fanout_stress_multicore_green.spl` source shape, Go-vs-Simple research,
  SimpleOS evidence docs, final SimpleOS AP ring/user handoff wording,
  handle-array native lowering, thread-spawn native regression coverage, and
  the concurrency API misuse inventory (`positive_fixtures=6`,
  `checked_in_misuse_fixtures=29`, `total_misuse_fixtures=40`).
- The shared default checkout remains dirty outside this lane because other
  sessions are active in WebGPU/UI/loader work. Multicore-green syncs continue
  in the separate jj workspace and must keep unrelated files out of lane
  commits unless the user explicitly asks for an integration commit.

## Current Sync Status (2026-06-14)

- Current multicore-green lane state is rebased on `main@origin`; unrelated
  remote GUI syncs have not touched the multicore-green owned paths.
- Go scheduler research is refreshed against official 2026-06-14 Go docs:
  the plan records Go 1.25 container-aware `GOMAXPROCS` defaults as domain
  context, but profile evidence remains pinned to `GOMAXPROCS=$CPU_WORKERS`.
- The current multicore-green doc/spec handoff keeps the report index,
  agent-task plan, system-test plan, tracking SSpec, and generated manual
  aligned with the 2026-06-14 SimpleOS evidence refresh without depending on a
  volatile pushed commit id.
- Status summaries use stable artifact names without depending on a volatile
  pushed commit id.
- The tracking SSpec and generated manual now assert that the SimpleOS report
  index, feature-tracking row, system-test plan, and agent-task handoff keep
  the 2026-06-14 refresh visible, so future agents do not treat older
  2026-06-13 hosted evidence as the latest state.
- Focused checks from the 2026-06-14 status-alignment slice passed: profile report
  contract, SPipe dev command wiring, local tracking SSpec with 13 scenarios,
  and `find doc/06_spec -name '*_spec.spl' | wc -l` returning `0`.
- The broader Go-like runtime roadmap remains `current`, not `done`: ordinary
  closure preemption, full scheduler-aware host M:N behavior, and ongoing
  profile parity work remain explicit follow-up gates.
