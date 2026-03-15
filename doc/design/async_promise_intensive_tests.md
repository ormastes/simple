# Async/Promise Intensive Tests — Design

## Pattern: Inline Stubs

All tests use **inline class/enum definitions** that mirror the real API. This is the proven pattern since the interpreter lacks SFFI modules. Each test file is self-contained.

## Stub Architecture

### Shared Stubs (repeated per file as needed)

```
Poll<T>         → enum { Ready(T), Pending } + is_ready/is_pending/unwrap/map
FutureState<T>  → enum { Pending, Ready(T), Failed(err) }
HostFuture<T>   → class with state, wakers, deadline + poll/map/then/catch/timeout/cancel
HostPromise<T>  → class with future + complete/fail/is_completed
Waker           → struct with task_id, scheduler_ref, wake_count
Context         → struct wrapping Waker
Task            → struct with id, priority, poll_fn, state
Executor        → class with tasks, ready_queue + spawn/run/block_on
Scheduler       → class with priority queues + schedule/run
WorkStealingQueue → class with local array + push/pop/steal
JoinSet         → class with task list + add_task/join_next/cancel_all
FuturesUnordered → class with futures list + push/try_next/len
Generator<Y,R>  → class with step_fn, state + next/send/is_complete
Channel         → class with buffer + send/recv/try_recv/close
```

## File Layout

```
test/system/async_promise_system_spec.spl           — E2E workflows
test/unit/lib/nogc_async_mut/promise_intensive_spec.spl
test/unit/lib/nogc_async_mut/host_future_intensive_spec.spl
test/unit/lib/nogc_async_mut/executor_scheduler_intensive_spec.spl
test/unit/lib/nogc_async_mut/combinators_intensive_spec.spl
test/unit/lib/nogc_async_mut/work_stealing_waker_intensive_spec.spl
test/unit/lib/nogc_async_mut/generator_intensive_spec.spl
test/unit/lib/nogc_async_mut/channel_intensive_spec.spl
```

## Related Documents

- [Requirement](../requirement/async_promise_intensive_tests.md)
- [Plan](../plan/async_promise_intensive_tests.md)
