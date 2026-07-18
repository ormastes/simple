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
- impl: Fixed the perf harness blocker by keeping `ThreadHandle`'s private handle field native-HIR friendly and removing an unsupported `Dict.remove` from the unused non-value task callback cleanup path.
- verify: `RUN_TIMEOUT=30 sh scripts/check/check-cross-language-perf.shs` completed with default `RUNS=20`; report: `doc/09_report/cross_language_perf_2026-06-05.md`. Simple native 100-worker OS-thread/channel parallel measured `12.863ms`; C pthreads `10.402ms`; Go goroutines `8.321ms`; Simple SMF parallel compiled but measured `fail` at runtime.
- investigate: A native `task_spawn` probe with four LCG tasks compiled, but `TaskHandle.join()` did not complete with the existing Simple-worker pool queue. An attempted shared-global queue fix compiled but caused runaway worker creation/native crash under gdb, so it was reverted. Tier 0 `<9ms` remained blocked on a runtime-owned pool submit path or a safe shared queue/worker lifecycle redesign.
- impl: Added runtime-owned pool ABI (`rt_pool_submit`, `rt_pool_join`, `rt_pool_is_done`) through `src/runtime/runtime_pool.c`, wired native codegen/runtime symbol discovery, and kept `thread_spawn` unchanged as the OS-thread API.
- impl: Updated `src/lib/nogc_async_mut/thread_pool.spl` so `task_spawn` prefers the runtime pool and falls back to the existing Simple registry path in interpreter or unavailable-runtime cases.
- impl: Added focused regression sources `test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl` and `test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_native.spl`.
- verify: Rebuilt isolated driver at `/tmp/simple-thread-pool-target/debug/simple`; `simple-native-all` and the core-C runtime archive builder both compile with `runtime_pool.c`.
- verify: `/tmp/simple-thread-pool-target/debug/simple check src/lib/nogc_async_mut/thread_pool.spl test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_native.spl` passed.
- verify: `SIMPLE_LIB=src /tmp/simple-thread-pool-target/debug/simple test test/01_unit/lib/nogc_async_mut/thread_pool_spec.spl --mode=interpreter --clean --sequential --timeout 60` passed with 4 examples.
- verify: `SIMPLE_LIB=src /tmp/simple-thread-pool-target/debug/simple test test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl --mode=interpreter --clean --sequential --timeout 60` passed with 1 file.
- verify: `SIMPLE_LIB=src /tmp/simple-thread-pool-target/debug/simple native-build --source src --source test/01_unit/lib/nogc_async_mut --entry test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_native.spl --entry-closure --clean --timeout 120 -o build/thread_enhancement/task_spawn_runtime_pool_native` linked a direct native smoke with concrete `T rt_pool_*` symbols; `build/thread_enhancement/task_spawn_runtime_pool_native` exited `0`.
- verify: `SIMPLE_LIB=src /tmp/simple-thread-pool-target/debug/simple test test/01_unit/lib/nogc_async_mut/green_thread_spec.spl --mode=interpreter --clean --sequential --timeout 60` passed with 3 examples.
- verify: `cc -std=gnu11 -pthread -c src/runtime/runtime_pool.c -o /tmp/runtime_pool_check.o` and `cc -std=c11 -D_GNU_SOURCE -pthread -c src/runtime/runtime_thread.c -o /tmp/runtime_thread_check.o` passed.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- note: Native SPipe BDD runner specs still segfault before test bodies when generated code calls unresolved `rt_bdd_*` symbols. The pool path was therefore verified with a direct native entry-closure smoke; the existing channel native failure under the rebuilt driver has the same `rt_bdd_*` cause, while `rt_channel_*` symbols are resolved in that binary.
