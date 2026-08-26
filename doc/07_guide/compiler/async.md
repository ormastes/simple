# Async/Await, Generators, and Actors

Covers asynchronous programming in Simple: lambdas, futures, async/await, generators, and the actor model.

## Current V1 foundation and status

SimpleRing/task/profile V1 is a pure-Simple contract foundation. It is not a
replacement runtime and it does not change the meaning of the existing
`Future`, `async`, `await`, green-thread, or OS-thread APIs.

| Contract | Current owner | What is covered now |
|----------|---------------|---------------------|
| `SimpleRing<Op, Cpl>` | `src/lib/nogc_async_mut/async_ring/simple_ring.spl` | Fixed-capacity, single-owner lifecycle, metadata/payload leases, cancellation, batches, and bounded latency/occupancy telemetry |
| Ring/task vocabulary | `src/lib/common/contracts/execution/simple_ring_async_v1.spl` | Tokens, typed completions, operation metadata, payload ownership, trace events, and callable `StacklessAsyncTask.poll` validation |
| Profile vocabulary | `src/lib/common/contracts/execution/async_profile_v1.spl` | `common`, `script`, `server`, `mission_alloc`, and `mission_pool` configuration records, fail-closed validation, canonical text, and fingerprints |
| Reference provider and mission evidence | `src/lib/nogc_async_mut/async_ring/software_provider.spl`, `mission_adapter.spl` | Bounded software mapping and hosted capacity admission; not a native or link-time-static mission runtime |
| Trace storage | `src/lib/nogc_async_mut_noalloc/async/async_trace_ring.spl` | Fixed-capacity, owner-bound trace records with explicit overflow policy; static placement is not proven |

The V1 contracts describe an explicit `poll(frame, context)` boundary and a
typed `Pending(wait_token)` result. They do not provide implicit-await
compiler lowering, a generated task-frame ABI, an executor migration, native
`io_uring` integration, or mission static task storage. The profile records are
configuration and validation data; a `mission_alloc` or `mission_pool` preset
does not itself allocate static storage or prove a mission runtime.

Existing `Future`/`HostFuture` values, async executors, cooperative green
queues, `task_spawn`, and `thread_spawn` remain compatibility or distinct
execution-model surfaces. They may be adapted to the V1 contracts later, but
none is silently promoted to the canonical V1 executor or task ABI.

---

## Lambda Expressions

Lambdas are anonymous functions that capture variables from their enclosing scope.

```simple
val square = \x: x * x
val add = \x, y: x + y
val answer = \: 42

val multiplier = 10
val scale = \x: x * multiplier    # Captures 'multiplier'
```

Immediately invoked:

```simple
val result = (\x: x + 10)(32)     # 42
```

Common use cases:

```simple
val doubled = items.map(\x: x * 2)
val evens = items.filter(\x: x % 2 == 0)
val sum = items.reduce(\acc, x: acc + x, 0)
```

**Limitation:** Captured variables are read-only. Mutations inside lambdas do not propagate back to the outer scope.

```simple
# Wrong - sum stays 0
var sum = 0
items.each(\x: sum = sum + x)

# Correct - use reduce
val sum = items.reduce(\acc, x: acc + x, 0)
```

---

## Futures and Await

The examples in this section document the established Future/await surface.
They are not evidence that V1 implicit suspension or compiler-generated frame
lowering is available. `await` remains an explicit compatibility language/API
surface until an executable compiler and runtime gate admits a new lowering.

Futures represent values that will be available later. `await` blocks until the future completes.

```simple
# Create deferred computations
val fut1 = future(\: fetch_user())
val fut2 = future(\: fetch_posts())

# Await results (runs concurrently)
val user = await fut1
val posts = await fut2
```

Error handling with Result:

```simple
async fn may_fail() -> Result<i64, Error>:
    if condition:
        Ok(42)
    else:
        Err(Error.new("Failed"))

match await may_fail():
    Ok(value): print "Success: {value}"
    Err(e): print "Error: {e.message}"
```

---

## Async Functions

Async functions return futures automatically and can use `await`.

```simple
async fn fetch_data() -> i64:
    val response = await http_get("https://api.example.com")
    response.parse_int()

async fn get_user_data(id: i64) -> User:
    val profile = await fetch_profile(id)
    val posts = await fetch_posts(id)
    User(profile: profile, posts: posts)

val data = await fetch_data()
```

---

## Generators and Yield

Generators produce sequences of values lazily using `yield`. They preserve state between calls.

```simple
val fibonacci = generator(\:
    var a = 0
    var b = 1
    while true:
        yield a
        val temp = a
        a = b
        b = temp + b
)

print fibonacci.next()    # Some(0)
print fibonacci.next()    # Some(1)
print fibonacci.next()    # Some(1)
print fibonacci.next()    # Some(2)
```

Generators are single-use. After exhaustion, `next()` returns `None`. Create a factory function to reuse:

```simple
fn make_range(start: i64, end: i64) -> Generator<i64>:
    generator(\:
        var i = start
        while i < end:
            yield i
            i = i + 1
    )

for x in make_range(0, 10): print x
for x in make_range(0, 10): print x    # Works (new generator)
```

---

## Actor Model

Actors are independent units of computation that communicate via messages.

```simple
actor Counter:
    var count: i64 = 0

    me increment():
        self.count = self.count + 1

    me get_count() -> i64:
        self.count

val counter = spawn Counter()
counter.send(Increment())
val count = await counter.ask(GetCount())
```

### Patterns

**Worker Pool:**

```simple
val workers = [for i in 0..10: spawn Worker()]
for task in tasks:
    workers[task.id % 10].send(task)
```

**Supervisor:**

```simple
actor Supervisor:
    var workers: List<Actor> = []

    me start():
        self.workers = [for i in 0..5: spawn Worker()]

    me restart_worker(id: i64):
        self.workers[id] = spawn Worker()
```

---

## Async Runtime

This section describes existing runtime-oriented vocabulary. The V1 foundation
adds value contracts around it; it does not select or replace a scheduler.

### Task ID Allocation

```simple
use std.async_sffi (task_alloc_id, NEXT_TASK_ID)

val id1 = task_alloc_id()
val id2 = task_alloc_id()
print "IDs: {id1}, {id2}"
```

### Waker System

```simple
use std.async_sffi (waker_signal, waker_check, waker_clear)

waker_signal(0, 5)           # Signal task 5
print waker_check(5)         # true
waker_clear(5)               # Clear
print waker_check(5)         # false
```

### Poll Type

```simple
enum Poll<T>:
    Ready(value: T)    # Completed
    Pending            # Not ready
```

### Runtime Selection

| Runtime | Capacity | Scheduling | Use Case |
|---------|----------|------------|----------|
| Embedded | 16 tasks, 32 futures | Cooperative | Microcontrollers, bare-metal |
| Host | Dynamic | Work-stealing | Servers, desktop apps |

---

## Performance

| Operation | Time |
|-----------|------|
| Lambda call | <1ns (inlined by compiler) |
| Future creation | ~10ns |
| Await (context switch) | ~50ns |
| Generator next() | ~20ns |
| Actor message | ~100ns |

---

## Best Practices

1. **Prefer lambdas for simple cases** over named functions
2. **Keep lambdas short** -- extract a named function if logic is complex
3. **Do not mutate captured variables** -- use `reduce` instead
4. **Handle future errors** explicitly with `match`
5. **Avoid blocking in async functions** -- use `await sleep()` not `thread_sleep()`
6. **Use generators for large sequences** to avoid memory allocation
7. **Batch actor messages** for throughput
8. **Run independent futures in parallel** -- create both, then await both

---

## Limitations

- Historical `async`, `await`, `yield`, `spawn`, and `generator` examples may
  be accepted by some compiler/parser paths, but that is not SimpleRing V1
  implicit-await or compiler-generated task-frame evidence
- Lambda capture is read-only
- Generators are single-use (exhausted after one iteration)
- No structured concurrency yet (no automatic cancellation of child tasks)
- SimpleRing V1 does not claim implicit-await insertion or compiler-generated task-frame lowering
- SimpleRing V1 has no canonical migrated executor, native `io_uring` provider, or proven link-time-static mission storage
- Existing Future, cooperative-green, pool-task, and OS-thread paths remain distinct until an adapter has executable parity evidence

---

## Related Files

- Async SFFI: `src/lib/nogc_async_mut/async_sffi.spl`
- SimpleRing/task contract: `src/lib/common/contracts/execution/simple_ring_async_v1.spl`
- SimpleRing implementation: `src/lib/nogc_async_mut/async_ring/simple_ring.spl`
- Async profiles: `src/lib/common/contracts/execution/async_profile_v1.spl`
- V1 unit specs: `test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl`, `test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl`, and `test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl`
- Async tests: `test/03_system/feature/async_features_spec.spl`
- Actor tests: `test/03_system/feature/actor_model_spec.spl`
- Syntax reference: `doc/07_guide/quick_reference/syntax_quick_reference.md`
