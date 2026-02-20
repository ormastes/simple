# Async/Await Implementation Plan

**Feature:** Asynchronous programming with `async`/`await` keywords
**Priority:** HIGH
**Impact:** 28 skipped tests (25 async + 3 await)
**Estimated Effort:** 4-6 sprints
**Status:** Planning

---

## Overview

Async/await enables non-blocking I/O and concurrent operations through cooperative multitasking.

### Syntax

```simple
# Async function definition
async fn fetch_data(url: text) -> text:
    val response = await http.get(url)
    await response.text()

# Async main
async fn main():
    val data = await fetch_data("https://api.example.com/data")
    print data

# Concurrent operations
async fn process_multiple():
    val results = await gather(
        fetch_data("url1"),
        fetch_data("url2"),
        fetch_data("url3")
    )
    return results
```

---

## Core Concepts

### 1. Future Type

```simple
# Future represents async computation
struct Future<T>:
    state: FutureState<T>
    waker: Waker?

enum FutureState<T>:
    Pending
    Ready(value: T)
    Error(error: text)

# Polling interface
trait Poll<T>:
    fn poll(waker: Waker) -> PollResult<T>

enum PollResult<T>:
    Ready(T)
    Pending
```

### 2. Async Function

```simple
# async fn returns Future<T>
async fn example() -> i64:
    42

# Equivalent to:
fn example() -> Future<i64>:
    Future.ready(42)
```

### 3. Await Operator

```simple
# await suspends until Future is ready
val result = await future

# Equivalent to:
val result = match future.poll(current_waker()):
    Ready(value): value
    Pending:
        suspend_and_reschedule()
        # Resume here when woken
        await future  # Retry poll
```

---

## Implementation Phases

### Phase 1: Core Types & Runtime (2 weeks)

**Future Type:**

```simple
# src/lib/async/future.spl
struct Future<T>:
    poll_fn: fn(Waker) -> PollResult<T>

    static fn ready(value: T) -> Future<T>:
        Future(poll_fn: \waker: PollResult.Ready(value))

    static fn pending() -> Future<T>:
        Future(poll_fn: \waker: PollResult.Pending)

    fn poll(waker: Waker) -> PollResult<T>:
        self.poll_fn(waker)

    fn and_then<U>(f: fn(T) -> Future<U>) -> Future<U>:
        # Future chaining
        ...

    fn map<U>(f: fn(T) -> U) -> Future<U>:
        # Future mapping
        ...
```

**Event Loop:**

```simple
# src/lib/async/runtime.spl
struct Runtime:
    task_queue: Queue<Task>
    wakers: Map<TaskId, Waker>

    fn spawn(future: Future<T>) -> TaskId:
        val task = Task(id: new_task_id(), future: future)
        self.task_queue.push(task)
        task.id

    fn run():
        while not self.task_queue.is_empty():
            val task = self.task_queue.pop()
            match task.future.poll(task.waker):
                Ready(value):
                    complete_task(task.id, value)
                Pending:
                    # Task will be re-queued when woken
                    ()

    fn block_on<T>(future: Future<T>) -> T:
        # Run until future completes
        self.spawn(future)
        self.run()
        get_task_result(future_id)
```

---

### Phase 2: Parser Support (1 week)

**Lexer:**
- Add `async` keyword
- Add `await` keyword

**Parser:**

```simple
fn parse_async_fn() -> FunctionDef:
    consume(Keyword("async"))
    consume(Keyword("fn"))
    val name = expect_identifier()
    val params = parse_params()
    consume(Arrow)
    val return_type = parse_type()
    consume(Colon)
    val body = parse_block()

    FunctionDef(
        name: name,
        params: params,
        return_type: Future(return_type),  # Wrap return type in Future
        body: body,
        is_async: true  # NEW flag
    )

fn parse_await_expr() -> Expr:
    consume(Keyword("await"))
    val future_expr = parse_expr()

    Expr(kind: ExprKind.Await(future_expr))
```

---

### Phase 3: Desugaring (2 weeks)

**Async Function Transformation:**

```simple
# Original:
async fn fetch(url: text) -> text:
    val response = await http.get(url)
    await response.text()

# Desugared:
fn fetch(url: text) -> Future<text>:
    Future.from_generator(\waker:
        # State machine:
        enum State:
            Start
            AwaitingResponse(response_future: Future<Response>)
            AwaitingText(text_future: Future<text>)
            Done

        var state = State.Start

        loop:
            match state:
                Start:
                    val response_future = http.get(url)
                    state = State.AwaitingResponse(response_future)

                AwaitingResponse(response_future):
                    match response_future.poll(waker):
                        Ready(response):
                            val text_future = response.text()
                            state = State.AwaitingText(text_future)
                        Pending:
                            return PollResult.Pending

                AwaitingText(text_future):
                    match text_future.poll(waker):
                        Ready(text):
                            state = State.Done
                            return PollResult.Ready(text)
                        Pending:
                            return PollResult.Pending

                Done:
                    error("polled after completion")
    )
```

**Await Transformation:**

```simple
# Original:
val result = await some_async_fn()

# Desugared:
val future = some_async_fn()
loop:
    match future.poll(current_waker()):
        Ready(value):
            val result = value
            break
        Pending:
            yield_to_runtime()
            # Resume here when woken
```

---

### Phase 4: Standard Library (2 weeks)

**Async I/O:**

```simple
# src/lib/async/io.spl
async fn read_file(path: text) -> text:
    val fd = await open_async(path)
    val content = await read_async(fd)
    await close_async(fd)
    content

async fn write_file(path: text, content: text):
    val fd = await create_async(path)
    await write_async(fd, content)
    await close_async(fd)
```

**Async HTTP:**

```simple
# src/lib/async/http.spl
async fn get(url: text) -> Response:
    val req = Request(method: "GET", url: url)
    await send_request(req)

async fn post(url: text, body: text) -> Response:
    val req = Request(method: "POST", url: url, body: body)
    await send_request(req)
```

**Combinators:**

```simple
# src/lib/async/combinators.spl
async fn gather<T>(futures: [Future<T>]) -> [T]:
    # Wait for all futures
    var results = []
    for future in futures:
        results.push(await future)
    results

async fn race<T>(futures: [Future<T>]) -> T:
    # Return first completed future
    ...

async fn timeout<T>(future: Future<T>, duration_ms: i64) -> Option<T>:
    # Complete within timeout or return None
    ...
```

---

### Phase 5: Integration & Testing (1 week)

**Test Framework:**

```simple
# Async tests
async_it "fetches data from API":
    val data = await fetch_json("https://api.test.com/data")
    check data["status"] == "ok"

# Timeout for async tests
#[timeout(5000)]
async_it "completes within timeout":
    await slow_operation()
```

**Examples:**

```simple
# examples/async/http_client.spl
async fn main():
    val urls = [
        "https://api1.com/data",
        "https://api2.com/data",
        "https://api3.com/data"
    ]

    val futures = urls.map(\url: fetch_data(url))
    val results = await gather(futures)

    for result in results:
        print result
```

---

## Comparison with Other Languages

| Language | Syntax | Runtime |
|----------|--------|---------|
| **Simple** | `async fn`, `await` | Green threads + event loop |
| JavaScript | `async`, `await` | Event loop (single-threaded) |
| Python | `async def`, `await` | asyncio event loop |
| Rust | `async fn`, `.await` | Tokio/async-std runtime |
| C# | `async`, `await` | Task-based async |

---

## Performance Considerations

### Benefits:
- Non-blocking I/O for high concurrency
- Lower memory than threads (10KB vs 2MB stack)
- No context switching overhead

### Trade-offs:
- Single-threaded by default (use thread pool for CPU work)
- State machine overhead (~100 bytes per async fn)
- Polling cost (~10ns per poll)

---

## Migration Path

### Phase 1: Simple -> Async

```simple
# Before (blocking):
fn fetch_and_process():
    val data = http.get("url")  # Blocks thread
    process(data)

# After (async):
async fn fetch_and_process():
    val data = await http.get("url")  # Yields to runtime
    process(data)
```

### Phase 2: Parallel -> Concurrent

```simple
# Before (parallel threads):
val threads = urls.map(\url: spawn_thread(\: fetch(url)))
val results = threads.map(\t: t.join())

# After (async):
val futures = urls.map(\url: fetch(url))
val results = await gather(futures)
```

---

## Alternative: Async by Default

Consider making async the default (like Go):

```simple
# Every function is implicitly async
fn fetch(url: text) -> text:
    val response = http.get(url)  # Automatically suspends
    response.text()

# Explicit blocking when needed
fn sync_fetch(url: text) -> text:
    block:
        http.get(url)  # Force blocking call
```

**Pros:**
- Simpler mental model
- No async/await keywords needed
- Less ceremony

**Cons:**
- Hidden suspension points
- Harder to reason about performance
- All code must be async-aware

**Recommendation:** Start with explicit async/await, consider async-by-default later based on user feedback.

---

## Success Criteria

1. ✅ Parser accepts `async fn` and `await`
2. ✅ Async functions return `Future<T>`
3. ✅ Event loop schedules and runs tasks
4. ✅ `await` suspends and resumes correctly
5. ✅ Async I/O operations work
6. ✅ `gather()` and `race()` combinators work
7. ✅ 28 skipped tests pass
8. ✅ Performance benchmarks (10K concurrent connections)

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 1. Core Types | 2 weeks | Future, Runtime, Waker |
| 2. Parser | 1 week | async/await syntax |
| 3. Desugaring | 2 weeks | State machine generation |
| 4. Stdlib | 2 weeks | Async I/O, HTTP, combinators |
| 5. Testing | 1 week | Tests, examples, docs |
| **Total** | **8 weeks** | **Feature complete** |

---

## Dependencies

- **Blocker:** None (can start now)
- **Enhanced by:** Generator support (for cleaner state machines)
- **Enables:** Non-blocking I/O, web servers, HTTP clients, concurrent systems
