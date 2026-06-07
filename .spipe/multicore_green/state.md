# Feature: multicore-green

## Raw Request

$sp_dev research about go thread. and others plan spawn agent plan and update doc and the profile scripts.  it should support m:n cpu pherallel like go. cooperative_green multicore_green should be supported. it also supported on simple os. if needed update simple os with sspec tests. however often sync with gh

## Task Type

feature

## Refined Goal

Deliver and verify a Simple concurrency lane that clearly separates OS threads, cooperative green threads, and pool-backed multicore green work while providing Go/C comparison evidence, SimpleOS evidence, current documentation, and profile-script gates.

## Acceptance Criteria

- AC-1: Go goroutine, C pthread, Simple `thread_spawn`, `cooperative_green_spawn`, `multicore_green_spawn`, and `task_spawn` semantics are researched and documented with no misleading M:N claims.
- AC-2: Public docs and coding guidance distinguish `thread_spawn` as OS-thread work, cooperative green APIs as current-carrier queue work, and `multicore_green_spawn` as pool-backed M:N candidate work only with runtime-pool evidence.
- AC-3: Profile scripts use existing canonical profile harnesses, include OS-thread, cooperative-green, multicore-green, Go, and C rows, and reject numbered API aliases such as `thread_spawn2`.
- AC-4: Perf reports prove Go-vs-C fanout behavior and Simple multicore-green native rows with `used_runtime_pool()` / `pool_used=` evidence.
- AC-5: Pure Simple implementation and generated workloads avoid unrolled numbered handles where compact semantic loops and handle arrays preserve behavior.
- AC-6: SimpleOS cooperative-green and multicore-green support has executable SPipe specs, generated manuals, and current evidence reports.
- AC-7: Misuse and API-shape checks reject wrong-surface imports, numbered API aliases, and fallback rows that pretend to be runtime-pool M:N work.
- AC-8: Final feature and NFR requirement documents are written from user-selected options; unselected options are removed per repository process.
- AC-9: Verification includes SPipe command wiring, generated-spec layout guard, relevant unit/system/perf specs, profile contract, and GitHub sync.

## Scope Exclusions

- Do not replace Simple user-facing concurrency APIs with C/Rust APIs.
- Do not claim cooperative green APIs are Go-style M:N CPU parallelism.

## Phase

dev-done

## Log

- dev: Created state file with acceptance criteria for the multicore green SPipe lane.
- audit: Current implementation/profile/docs evidence is present for AC-1 through
  AC-9 after selected requirements were written.
- requirements: User selected `Full Go-Like Runtime Roadmap`; final feature and
  NFR requirements were written and option docs were removed.
- implementation: Added hosted multicore-green parallelism control through
  `multicore_green_set_parallelism` / `multicore_green_parallelism` and
  `rt_pool_set_parallelism` / `rt_pool_get_parallelism`; profile rows now
  require `parallelism=requested/actual` evidence in addition to `pool_used`.
- verification: Re-ran SimpleOS cooperative green, multicore green scheduler,
  green-channel wake, default QEMU gate, and live QEMU green-carrier proof with
  the rebuilt compiler; live QEMU passed in 40469ms.

## Completion Audit - 2026-06-07

### Proven Or Strong Evidence

- AC-1 / AC-2: `doc/01_research/lib/threading/go_vs_simple_threads.md`,
  `doc/01_research/local/multicore_green.md`,
  `doc/01_research/domain/multicore_green.md`,
  `doc/07_guide/lib/misc/stdlib.md`,
  `doc/07_guide/compiler/check_perf.md`, and
  `.codex/skills/coding/SKILL.md` distinguish OS threads, cooperative green
  work, runtime-pool multicore green work, Go goroutines, C pthreads, and
  `task_spawn`.
- AC-3 / AC-4 / AC-5: `scripts/check/check-cross-language-perf.shs`,
  `doc/09_report/cross_language_perf_parallel_smoke.md`, and
  `test/05_perf/profile_scripts/profile_report_contract_test.shs` use the
  canonical profile harness, compact handle-array generated workloads, Go/C
  comparison rows, and `pool_used=` evidence while rejecting numbered aliases.
- AC-6: `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl`,
  `test/03_system/os/simpleos/feature/simpleos_multicore_green_spec.spl`,
  their generated manuals under `doc/06_spec/03_system/os/simpleos/feature/`,
  and `doc/09_report/simpleos_multicore_green_evidence_2026-06-07.md` provide
  current SimpleOS evidence.
- AC-7: `test/03_system/feature/usage/multicore_green_tracking_spec.spl`,
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`, and the
  profile report contract reject wrong-surface claims, numbered API names, and
  runtime-pool fallback rows.
- AC-9: Recent guards include `sh scripts/setup/install-spipe-dev-command.shs
  --check`, `find doc/06_spec -name '*_spec.spl' | wc -l` returning `0`,
  `test/05_perf/stress/multicore_green_cross_language_gate_spec.spl`, and the
  cross-language profile report contract. GitHub is synced through this lane.

### Requirement Selection Complete

- AC-8 is satisfied by `doc/02_requirements/feature/multicore_green.md` and
  `doc/02_requirements/nfr/multicore_green.md`.
- The selected feature scope is `Full Go-Like Runtime Roadmap`.
- The selected NFR path is Evidence Integrity Gate, Performance Parity Budget,
  API Stability And Misuse Diagnostics, and SimpleOS Hardware Proof Gate.
