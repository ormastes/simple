# Async/Await, Generators, and Actors

> **2026-10-27 status:** this guide mixes language examples and runtime-family
> APIs. Check the selected compiler/provider capability before using an example
> as an availability claim. The [async infrastructure architecture](../../04_architecture/language/async_infrastructure.md)
> records existing hosted futures/promises, scheduler contexts and native
> I/O/fiber paths, plus their pending-chain/join and cross-thread gaps.
> `std.async` is the intended shared interface; `async_host` supplies hosted
> execution. Existing `async_host`, `async_embedded` and `async_unified`
> imports remain compatible during the proposed facade migration.

Covers asynchronous programming in Simple: lambdas, futures, async/await, generators, and the actor model.

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

```text
val doubled = items.map(\x: x * 2)
val evens = items.filter(\x: x % 2 == 0)
val sum = items.reduce(\acc, x: acc + x, 0)
```

**Limitation:** Captured variables are read-only. Mutations inside lambdas do not propagate back to the outer scope.

```text
# Wrong - sum stays 0
var sum = 0
items.each(\x: sum = sum + x)

# Correct - use reduce
val sum = items.reduce(\acc, x: acc + x, 0)
```

---

## Futures and Await

Futures represent values that may become available later. Under the target
managed-task contract, `await` suspends the task until completion; it must not
block the carrier thread. A synchronous root may explicitly drive an executor.
Actual language lowering and provider support require separate qualification.

```text
# Create deferred computations
val fut1 = future(\: fetch_user())
val fut2 = future(\: fetch_posts())

# Await results (runs concurrently)
val user = await fut1
val posts = await fut2
```

Error handling with Result:

```text
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

```text
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

```text
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

```text
val workers = [for i in 0..10: spawn Worker()]
for task in tasks:
    workers[task.id % 10].send(task)
```

**Supervisor:**

```text
actor Supervisor:
    var workers: List<Actor> = []

    me start():
        self.workers = [for i in 0..5: spawn Worker()]

    me restart_worker(id: i64):
        self.workers[id] = spawn Worker()
```

---

## Async Runtime

### Task ID Allocation

```simple
use std.nogc_async_mut.async_sffi.{task_alloc_id, NEXT_TASK_ID}

val id1 = task_alloc_id()
val id2 = task_alloc_id()
print "IDs: {id1}, {id2}"
```

### Waker System

The following is the legacy `async_sffi` compatibility surface. Its task-ID
table is not the canonical generation-qualified cross-thread wake contract.
New shared-resource integrations use the existing task/ring contracts and a
qualified executor ingress; a manually set flag does not wake a sleeping OS
carrier by itself.

```simple
use std.nogc_async_mut.async_sffi.{waker_signal, waker_check, waker_clear}

waker_signal(0, 5)           # Signal task 5
print waker_check(5)         # true
waker_clear(5)               # Clear
print waker_check(5)         # false
```

### Poll Type

```text
enum Poll<T>:
    Ready(value: T)    # Completed
    Pending            # Not ready
```

### Runtime Selection

These are runtime-family descriptions, not portable capacity/performance
guarantees. Inspect the selected provider and compile-time exports. The current
`async_unified` module documents host default and incomplete runtime selection.

| Runtime | Capacity | Scheduling | Use Case |
|---------|----------|------------|----------|
| Embedded | 16 tasks, 32 futures | Cooperative | Microcontrollers, bare-metal |
| Host | Dynamic | Work-stealing | Servers, desktop apps |

---

## Performance evidence

No reproducible source/provider/workload receipt accompanies the previous
nanosecond estimates, so they are not performance guarantees. Measure handle
latency, first usable result, wake tail latency, throughput and retained memory
on the actual selected backend. See the
[async TDD and measurement plan](../../03_plan/sys_test/async_infrastructure.md).

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

- Syntax and lowering support differ by compiler/interpreter profile; require
  actual compile/run evidence for `async`, `await`, `yield`, `spawn` and
  `generator` rather than inferring support from a library type.
- Lambda capture is read-only
- Generators are single-use (exhausted after one iteration)
- Hosted task contexts already carry lifetime/cancellation and cleanup
  machinery. Complete parent/child cancellation, result publication and native
  cleanup across every provider remain separate qualification gates.
- Pending HostFuture map/then and HostTaskHandle join need live subscription
  hardening at the audited source pin; ready-only examples do not verify it.

---

## Related Files

- Async SFFI: `src/lib/nogc_async_mut/async_sffi.spl`
- Async tests: `test/03_system/feature/async_features_spec.spl`
- Actor tests: `test/03_system/feature/actor_model_spec.spl`
- Syntax reference: `doc/07_guide/quick_reference/syntax_quick_reference.md`
