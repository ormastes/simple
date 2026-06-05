# Feature: thread_enhancement

## Raw Request
$sp_dev impl with spawn agent thread_enhancement_plan.md and test intensively.

## Task Type
feature

## Refined Goal
Implement the thread enhancement plan by delivering a pool-backed task-spawn slice with correctness tests, preserving OS-thread `thread_spawn`, and preparing independently owned follow-up lanes for green-thread and preemption work.

## Acceptance Criteria
- AC-1: `doc/03_plan/runtime/thread_enhancement_plan.md` remains the source plan and records current implementation evidence, owned lanes, and remaining tier gates.
- AC-2: A pool-backed task spawn API exists in Simple stdlib code without changing the explicit OS-thread `thread_spawn` API.
- AC-3: A cooperative green-thread API exists with `GreenThreadHandle`, `green_spawn`, `green_run_one`, and `green_run_all`, separate from OS-thread `ThreadHandle`.
- AC-4: Thread pool waiting does not rely on millisecond sleep polling in the implemented path.
- AC-5: Channel full-buffer behavior has a regression test or explicit verification evidence showing no silent drop in the changed path.
- AC-6: Spawn-agent lane outputs identify runtime, stdlib, compiler/preemption, and verification responsibilities with concrete files and gates.
- AC-7: Focused thread/channel/spawn tests pass in at least interpreter mode; native or broader mode failures are recorded with exact commands and causes.
- AC-8: Intensive verification includes the SPipe doc layout guard, relevant thread/channel tests, and the cross-language performance harness or a documented reason it cannot complete.

## Scope Exclusions
- Full Tier 1 green-thread scheduler productionization is not required before the Tier 0 pool-backed spawn slice lands.
- Tier 2 growable stacks and compiler preemption are design-spike outputs unless the lower tiers are already complete.
- `thread_spawn` remains the low-level OS-thread primitive and is not replaced.

## Phase
dev-done

## Log
- dev: Created state file with 7 acceptance criteria (type: feature).
- dev: Added explicit green-thread API acceptance criterion after user requested OS-thread and green-thread support.
- impl: Added cooperative green-thread module at `src/lib/nogc_async_mut/concurrent/green_thread.spl`.
- impl: Added focused OS-thread plus green-thread spec at `test/01_unit/lib/nogc_async_mut/green_thread_spec.spl`.
- verify: `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/green_thread_spec.spl --mode=interpreter --clean --sequential --timeout 60` passed with 3 examples.
- verify: `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl --mode=interpreter --clean --sequential --timeout 60` passed with 4 examples.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- impl: Changed native C channel send to grow the ring buffer instead of silently dropping when the old 1024-slot capacity is reached.
- impl: Added `test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl`.
- impl: Corrected the native overflow spec to use the runtime `i64` channel ABI; removed the standalone native-build helper because it is not the authoritative SPipe runner path.
- verify: `SIMPLE_LIB=src bin/simple test test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl --mode=native --clean --force-rebuild --sequential --timeout 120` passed with 1 example.
- verify: `sh scripts/check/check-cross-language-perf.shs` was attempted. It reported `[FAIL] Simple native: build/cross_lang_perf/parallel.spl` and `[FAIL] Simple SMF: build/cross_lang_perf/parallel.spl`, then stalled in `=== Measuring parallel - 100 workers ===`; the current harness process tree was terminated after no further output.
