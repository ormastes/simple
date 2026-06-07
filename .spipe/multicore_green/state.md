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
- Do not mark the feature complete until final feature/NFR requirement options are selected and written.

## Phase

dev-done

## Log

- dev: Created state file with acceptance criteria for the multicore green SPipe lane.
