# Async/Promise Intensive Tests — Plan

## Objective
Create intensive test suite for the async/promise library covering all major components with 150+ test cases using inline stubs (proven pattern for interpreter mode).

## Current Status
| Component | Status | Evidence |
|-----------|--------|----------|
| Promise basic | Real | test/unit/lib/nogc_async_mut/promise_spec.spl (17 it blocks) |
| Promise chaining/combinators | Missing | No then/catch/all/race tests |
| Async core types (Poll, TaskState, etc.) | Real | test/unit/lib/nogc_async_mut/async_spec.spl (10 it blocks) |
| HostFuture/HostPromise | Skipped | async_host_spec.spl all commented out |
| Executor/Scheduler | Stub only | async_spec.spl has trivial stubs |
| Combinators (join_all/select/race) | Missing | No tests |
| JoinSet/FuturesUnordered | Missing | All commented out in async_host_spec.spl |
| WorkStealingQueue | Missing | All commented out |
| Waker/Context | Missing | All commented out |
| Generator | Skipped | "interpreter runtime issue" |
| Channel | Real (imports) | concurrent_spec.spl has basic tests |
| Concurrent collections | Real (imports) | concurrent_spec.spl has 30+ tests |
| System tests | Missing | No test/system/ for async |

## What To Do

1. **Create system test** `test/system/async_promise_system_spec.spl` — end-to-end workflows (difficulty: 3)
2. **Expand promise tests** `test/unit/lib/nogc_async_mut/promise_intensive_spec.spl` — chaining, combinators, error propagation (difficulty: 2)
3. **Create HostFuture intensive tests** `test/unit/lib/nogc_async_mut/host_future_intensive_spec.spl` — all HostFuture operations with inline stubs (difficulty: 3)
4. **Create HostPromise intensive tests** — integrated into host_future_intensive_spec.spl (difficulty: 2)
5. **Create executor/scheduler tests** `test/unit/lib/nogc_async_mut/executor_scheduler_intensive_spec.spl` — task lifecycle, priority scheduling (difficulty: 3)
6. **Create combinator tests** `test/unit/lib/nogc_async_mut/combinators_intensive_spec.spl` — join_all, select, race, timeout (difficulty: 2)
7. **Create work-stealing/waker tests** `test/unit/lib/nogc_async_mut/work_stealing_waker_intensive_spec.spl` — LIFO/FIFO, wake tracking (difficulty: 2)
8. **Create generator tests** `test/unit/lib/nogc_async_mut/generator_intensive_spec.spl` — yield/next/send with inline stubs (difficulty: 2)
9. **Create channel intensive tests** `test/unit/lib/nogc_async_mut/channel_intensive_spec.spl` — stress tests, edge cases (difficulty: 2)

## Dependencies (DAG)
```
1 (system test skeleton) → depends on 2-8 being designed
2 (promise) → independent
3 (host future) → independent
4 (host promise) → uses 3's stubs
5 (executor) → independent
6 (combinators) → uses 3's patterns
7 (work-stealing) → independent
8 (generator) → independent
9 (channel) → independent
```

## Test File Summary
| File | Target it blocks | Components |
|------|-----------------|------------|
| promise_intensive_spec.spl | 25+ | Promise chaining, combinators, error propagation |
| host_future_intensive_spec.spl | 30+ | HostFuture, HostPromise, FutureState |
| executor_scheduler_intensive_spec.spl | 25+ | Executor, Scheduler, Task, Runtime |
| combinators_intensive_spec.spl | 20+ | join_all, select, race, timeout |
| work_stealing_waker_intensive_spec.spl | 20+ | WorkStealingQueue, Waker, Context |
| generator_intensive_spec.spl | 15+ | Generator, GeneratorState |
| channel_intensive_spec.spl | 15+ | Channel stress tests |
| async_promise_system_spec.spl | 10+ | End-to-end workflows |
| **Total** | **160+** | |
