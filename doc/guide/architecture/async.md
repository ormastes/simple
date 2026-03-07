# Async/Await, Generators, and Actors

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

- `async`, `await`, `yield`, `spawn`, `generator` keywords work in the compiler but are not yet in the runtime parser
- Lambda capture is read-only
- Generators are single-use (exhausted after one iteration)
- No structured concurrency yet (no automatic cancellation of child tasks)

---

## Related Files

- Async SFFI: `src/lib/nogc_async_mut/async_sffi.spl`
- Async tests: `test/feature/async_features_spec.spl`
- Actor tests: `test/feature/actor_model_spec.spl`
- Syntax reference: `doc/guide/quick_reference/syntax_quick_reference.md`
