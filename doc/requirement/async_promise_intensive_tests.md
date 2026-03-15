# Async/Promise Intensive Tests — Requirement

**Feature:** Intensive test suite for async libs (promise, future, executor, combinators, concurrency)
**Category:** Testing
**Status:** In Progress
**Date:** 2026-03-15

## Motivation

The async/promise library in `src/lib/nogc_async_mut/` has extensive source code but sparse test coverage. Most existing tests use trivial stubs or are skipped due to missing SFFI modules in interpreter mode. We need intensive tests that exercise the logic deeply using inline implementations (the pattern that works in interpreter mode).

## Scope

### In Scope

1. **Promise** — Chaining (then/catch/finally), combinators (all/race/allSettled/any), error propagation, nested promises, callback ordering
2. **Future/HostFuture** — poll, map, flat_map, then, catch, timeout, cancel, delay, state transitions, FutureState enum
3. **HostPromise** — complete, fail, double-complete prevention, future-promise pairing
4. **Poll** — Ready/Pending pattern matching, unwrap, map, is_ready/is_pending
5. **Executor** — spawn, run, run_iteration, block_on, task lifecycle, cooperative scheduling
6. **Scheduler** — priority-based scheduling, high/normal/low priority tasks
7. **Runtime** — global runtime, spawn, block_on
8. **Combinators** — join_all, select, race, timeout, retry, zip
9. **JoinSet** — spawn tasks, join_next, join_all, cancel_all, dynamic growth
10. **FuturesUnordered** — push, try_next, poll_next, dynamic collection
11. **WorkStealingQueue** — push, pop (LIFO), steal (FIFO), empty state
12. **Waker/Context** — wake, wake_by_ref, will_wake, wake_count tracking
13. **CancellationToken** — cancel, check, is_cancelled, cooperative cancellation
14. **Channel** — send, recv, try_recv, close, is_closed, capacity
15. **Concurrent collections** — stress tests for MpscQueue, MpmcQueue, ConcurrentMap
16. **Generator** — yield_value, next, send, GeneratorState, resume, complete
17. **System tests** — End-to-end async workflows combining multiple components

### Out of Scope

- Tests requiring actual multi-threading SFFI (those remain skipped)
- Tests requiring actual async I/O (file, TCP, UDP)
- GPU/CUDA async tests
- ML pipeline async tests (already exist)

## I/O Examples

### Example 1: Promise chaining
```simple
val p = make_resolved(21)
val chained = p.then(\v: v * 2)
# chained should resolve to 42
```

### Example 2: Promise.all
```simple
val promises = [make_resolved(1), make_resolved(2), make_resolved(3)]
val all = Promise.all(promises)
# all resolves to [1, 2, 3]
```

### Example 3: Future combinators
```simple
val futures = [HostFuture.ready(1), HostFuture.ready(2)]
val joined = join_all(futures)
# joined is Ready([1, 2])
```

### Example 4: Executor task lifecycle
```simple
val executor = Executor.new()
executor.spawn(Task.new(\: 42))
executor.run()
# All tasks complete
```

### Example 5: WorkStealingQueue LIFO/FIFO
```simple
var q = WorkStealingQueue.new()
q.push(1); q.push(2); q.push(3)
q.pop()   # -> 3 (LIFO)
q.steal() # -> 1 (FIFO)
```

## Acceptance Criteria

1. **AC-01:** System test file covers all 17 scope items with at least 3 scenarios each
2. **AC-02:** Promise chaining tests cover: then, catch, finally, nested chains, error propagation
3. **AC-03:** Combinator tests cover: join_all, select, race, timeout with ready/pending/mixed futures
4. **AC-04:** Executor tests cover: spawn, run, task completion, multiple tasks, empty executor
5. **AC-05:** All tests use inline stubs (matching real API) since interpreter mode lacks SFFI
6. **AC-06:** Edge cases tested: nil values, empty collections, double-completion, already-resolved
7. **AC-07:** At least 150 `it` blocks across all test files
8. **AC-08:** All tests pass with `bin/simple test`
9. **AC-09:** Tests follow SSpec conventions (to_equal, to_be, etc.)

## Dependencies

- Existing async source in `src/lib/nogc_async_mut/async/` and `src/lib/nogc_async_mut/async_host/`
- SSpec test runner
- Inline stub pattern (proven in existing `promise_spec.spl` and `async_spec.spl`)

## Related Documents

- [Plan](../plan/async_promise_intensive_tests.md)
- [Design](../design/async_promise_intensive_tests.md)
