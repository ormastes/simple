# Async-Default Function Model

**Status:** Draft
**Feature IDs:** #276-285
**Last Updated:** 2026-01-05
**Keywords:** async, sync, effects, promises, futures
**Topics:** concurrency, syntax, effects

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

## Related Specifications

- [Suspension Operator](suspension_operator.md) - Explicit `~` suspension syntax
- [Concurrency](concurrency.md) - Futures, actors, channels
- [Functions](functions.md) - Function definitions

---

## Motivation

Most modern applications are I/O-bound and async. Requiring `async` on every function leads to:

```simple
# Verbose: async everywhere
async fn fetch_user(id: UserId) -> User: ...
async fn fetch_orders(user: User) -> [Order]: ...
async fn fetch_products(order: Order) -> [Product]: ...
async fn main():
    let user = await fetch_user(1_uid)
    let orders = await fetch_orders(user)
    ...
```

**Observation:** In real codebases, 80%+ of functions could be async. Making sync explicit is more practical.

---

## Design Overview

### Core Principle: Async is Default

| Declaration | Meaning | Can Suspend? |
|-------------|---------|--------------|
| `fn foo()` | Async-capable (default) | ✅ Yes |
| `sync fn foo()` | Explicitly synchronous | ❌ No |

### Return Type: Implicit Promise Wrapping

Functions that **can** suspend have their return type implicitly wrapped:

```simple
# Declaration
fn fetch_user(id: UserId) -> User

# Actual signature (implicit)
fn fetch_user(id: UserId) -> Promise[User]
```

But the caller sees the **unwrapped** type when using `~=` or `await`:

```simple
let user ~= fetch_user(1_uid)   # user: User (not Promise[User])
```

---

## Syntax

### Function Declarations

```simple
# Async-capable (default) - can contain ~=, if~, while~
fn load_data() -> Data:
    let content ~= read_file(path)
    return parse(content)

# Explicitly sync - compile error if tries to suspend
sync fn compute(x: i64) -> i64:
    return x * 2

# Actor handlers - always run-to-completion (implicitly sync-like)
actor Counter:
    on Increment(n: i64):      # Cannot suspend
        self.value += n
```

### Calling Conventions

```simple
fn caller() -> Result:
    # Suspending call - awaits and unwraps
    let data ~= load_data()           # data: Data

    # Non-suspending call - gets the Promise
    let promise = load_data()          # promise: Promise[Data]

    # Sync function - no promise wrapping
    let result = compute(42)           # result: i64 (direct)
```

---

## Promise Type

### Definition

```simple
enum PromiseState:
    Pending
    Fulfilled
    Rejected

class Promise[T]:
    state: PromiseState
    value: Option[T]
    error: Option[Error]
```

### Implicit Wrapping Rules

| Function Type | Declared Return | Actual Return | Call with `~=` |
|---------------|-----------------|---------------|----------------|
| `fn` (default) | `T` | `Promise[T]` | `T` |
| `fn` (default) | `Promise[T]` | `Promise[T]` | `T` |
| `sync fn` | `T` | `T` | N/A (error) |

### Explicit Promise Return

If you explicitly return `Promise[T]`, no double-wrapping:

```simple
fn get_cached_or_fetch(id: UserId) -> Promise[User]:
    if let Some(user) = cache.get(id):
        return Promise.resolve(user)   # Already resolved
    return fetch_user(id)              # Returns Promise[User]
```

---

## Combinators (Promise Chaining)

### then() / catch() / finally()

```simple
fn process_pipeline() -> Promise[Result]:
    return fetch_data()
        .then(\data: transform(data))
        .then(\transformed: save(transformed))
        .catch(\err: log_error(err); default_result())
        .finally(\: cleanup())
```

### all() / race() / any()

```simple
fn parallel_fetch(ids: [UserId]) -> Promise[[User]]:
    let promises = ids.map(\id: fetch_user(id))
    return Promise.all(promises)

fn first_response(urls: [Url]) -> Promise[Response]:
    let promises = urls.map(\url: http.get(url))
    return Promise.race(promises)

fn first_success(urls: [Url]) -> Promise[Response]:
    let promises = urls.map(\url: http.get(url))
    return Promise.any(promises)   # First non-rejected
```

### allSettled()

```simple
fn try_all(tasks: [Task]) -> Promise[[SettledResult[T]]]:
    let promises = tasks.map(\t: run_task(t))
    return Promise.all_settled(promises)

# SettledResult is:
enum SettledResult[T]:
    Fulfilled(value: T)
    Rejected(error: Error)
```

---

## Sync Functions

### Declaration

```simple
sync fn pure_compute(x: i64, y: i64) -> i64:
    return x + y

sync fn validate(data: Data) -> bool:
    return data.is_valid()
```

### Restrictions

```simple
sync fn bad_sync():
    let x ~= fetch()        # ERROR: suspension in sync function
    if~ is_ready():         # ERROR: suspending guard in sync
        ...

sync fn also_bad():
    let p = fetch()         # OK: just getting the Promise
    let x = await p         # ERROR: await in sync function
```

### When to Use `sync`

1. **Pure computation** - No I/O, no side effects
2. **Performance critical** - Guaranteed no scheduling overhead
3. **FFI callbacks** - C functions can't handle suspension
4. **Actor handlers** - Run-to-completion semantics

---

## Type Inference

### Promise Inference

```simple
fn example():
    # Type inference handles unwrapping
    let user ~= fetch_user(id)      # user: User
    let data ~= load_config()       # data: Config

    # Without ~=, you get the Promise
    let p = fetch_user(id)          # p: Promise[User]

    # Sync functions return directly
    let n = compute(42)             # n: i64
```

### Generic Functions

```simple
# Works with any async function
fn retry[T](f: fn() -> T, attempts: i64) -> T:
    for i in 0..attempts:
        match f():
            case Ok(v): return v
            case Err(e) if i < attempts - 1:
                _ ~= timer.sleep(1000_ms)
            case Err(e):
                return Err(e)
```

### Sync Constraint

```simple
# Only accepts sync functions
sync fn map_sync[T, U](items: [T], f: sync fn(T) -> U) -> [U]:
    return [f(item) for item in items]

# Accepts any function (async or sync)
fn map_async[T, U](items: [T], f: fn(T) -> U) -> [U]:
    return [f(item) ~= for item in items]  # Parallel await
```

---

## Effect Inference (Automatic async/sync Detection)

Simple uses **bidirectional effect inference** to automatically determine whether a function is async or sync based on its body. No explicit annotation is needed in most cases.

### Inference Rules

| Function Body Contains | Inferred Effect | Return Type |
|------------------------|-----------------|-------------|
| `~=`, `if~`, `while~`, `for~` | async | `Promise[T]` |
| Calls to async functions | async | `Promise[T]` |
| Only sync operations | sync | `T` directly |

### Examples

```simple
# INFERRED AS SYNC: only pure computation
fn double(x: i64) -> i64:
    return x * 2
# Compiler infers: sync fn double(x: i64) -> i64

# INFERRED AS ASYNC: uses ~= operator
fn get_user_name(id: UserId) -> str:
    let user ~= fetch_user(id)
    return user.name
# Compiler infers: fn get_user_name(id: UserId) -> Promise[str]

# INFERRED AS ASYNC: calls async function (even without ~=)
fn get_promise(id: UserId) -> User:
    return fetch_user(id)    # Returns Promise[User]
# Compiler infers: fn get_promise(id: UserId) -> Promise[User]

# INFERRED AS SYNC: only calls sync functions
fn compute_total(items: [Item]) -> i64:
    return items.map(\i: i.price).sum()
# Compiler infers: sync fn compute_total(items: [Item]) -> i64
```

### Inference Algorithm

```
infer_effect(fn_body):
    1. Collect all expressions in fn_body
    2. For each expression:
       - If suspension operator (~=, if~, while~, for~): return ASYNC
       - If function call f():
         - If f is known async: return ASYNC
         - If f is known sync: continue
         - If f is unknown: defer (mutual recursion)
    3. If no async indicators found: return SYNC
    4. For deferred cases: use fixed-point iteration
```

### Call-Site Inference

The compiler also infers at call sites:

```simple
fn caller() -> Data:
    # fetch_data() returns Promise[Data]
    # Assigning to Data (not Promise[Data]) implies await
    let data: Data = fetch_data()    # Implicit ~= inferred!
    return data

# Equivalent to:
fn caller() -> Data:
    let data ~= fetch_data()
    return data
```

### Type-Driven Await Inference

```simple
fn example():
    let p = fetch_user(id)      # p: Promise[User] (no await)
    let u: User = fetch_user(id) # u: User (await inferred from type)
    let v ~= fetch_user(id)      # v: User (explicit await)
```

| Assignment | Target Type | Inferred |
|------------|-------------|----------|
| `let p = async_fn()` | `Promise[T]` | No await |
| `let x: T = async_fn()` | `T` | Await inferred |
| `let y ~= async_fn()` | `T` | Explicit await |

### Explicit Override

Use `sync` to **force** sync semantics (compiler verifies):

```simple
# Force sync - error if body would suspend
sync fn must_be_fast(x: i64) -> i64:
    return x * x              # OK: pure computation

sync fn broken():
    let x ~= fetch()          # ERROR: suspension in sync fn

sync fn also_broken():
    let x: Data = fetch()     # ERROR: type-inferred await in sync fn
```

### Async Boundary Annotation

For public APIs, you can explicitly declare the effect for documentation:

```simple
# Explicit async (documentation, no behavioral change)
async fn fetch_user(id: UserId) -> User:
    ...

# Explicit sync (enforced by compiler)
sync fn compute(x: i64) -> i64:
    ...

# Inferred (most common case)
fn process(data: Data) -> Result:
    ...  # Compiler figures it out
```

### Mutual Recursion

The compiler handles mutually recursive functions:

```simple
fn ping(n: i64) -> i64:
    if n == 0: return 0
    return pong(n - 1)        # Calls pong

fn pong(n: i64) -> i64:
    if n == 0: return 0
    return ping(n - 1)        # Calls ping

# Both inferred as SYNC (no suspension in either)
```

```simple
fn async_ping(n: i64) -> i64:
    if n == 0: return 0
    _ ~= delay(10_ms)         # Suspension!
    return async_pong(n - 1)

fn async_pong(n: i64) -> i64:
    if n == 0: return 0
    return async_ping(n - 1)  # Calls async function

# Both inferred as ASYNC (async_ping suspends, async_pong calls it)
```

### Inference Summary

```
┌─────────────────────────────────────────────────────────────┐
│                    Effect Inference Flow                      │
├─────────────────────────────────────────────────────────────┤
│                                                               │
│  fn foo() -> T:                                              │
│      body...                                                  │
│          │                                                    │
│          ▼                                                    │
│  ┌───────────────────┐                                       │
│  │ Analyze body for: │                                       │
│  │ - ~=, if~, while~ │──yes──▶ ASYNC, returns Promise[T]    │
│  │ - async fn calls  │                                       │
│  │ - type-driven     │                                       │
│  │   await (T = ...)│                                       │
│  └───────────────────┘                                       │
│          │ no                                                 │
│          ▼                                                    │
│      SYNC, returns T directly                                │
│                                                               │
└─────────────────────────────────────────────────────────────┘
```

---

## Interaction with ~= Operator

### In Async-Default Functions

```simple
fn process() -> Data:
    # ~= is the standard way to call and await
    let raw ~= fetch_data()
    let parsed ~= parse_async(raw)
    return transform(parsed)
```

### In Sync Functions

```simple
sync fn compute() -> i64:
    # ~= is a compile error
    let x ~= fetch()    # ERROR

    # Getting promise is OK, but can't await it
    let p = fetch()     # OK: p is Promise[i64]
    # But what can you do with it? Not much in sync context
```

### Bridging Sync and Async

```simple
# Spawn async work from sync context
sync fn start_background_task(id: TaskId):
    spawn_detached:
        let result ~= long_running_task(id)
        notify_complete(id, result)

# Block on async from sync (escape hatch)
sync fn blocking_fetch(id: UserId) -> User:
    return block_on(fetch_user(id))   # Blocks thread!
```

---

## Migration Strategy

### Phase 1: Add `sync` Keyword

```simple
# Old code still works
fn foo() -> i64:
    return 42

# Can now mark sync explicitly
sync fn bar() -> i64:
    return 42
```

### Phase 2: Warn on Implicit Sync

```simple
# Warning: function 'foo' could be marked 'sync'
fn foo() -> i64:
    return 42

# No warning
sync fn foo() -> i64:
    return 42
```

### Phase 3: Async-Default Semantics

```simple
# Now fn is async by default
fn foo() -> i64:         # Returns Promise[i64]
    return 42

sync fn bar() -> i64:    # Returns i64 directly
    return 42
```

### Migration Tool

```bash
# Analyze codebase for sync-eligible functions
simple migrate --analyze-sync

# Auto-add sync to non-suspending functions
simple migrate --add-sync

# Verify no behavior changes
simple migrate --verify
```

---

## Comparison with Other Languages

| Language | Default | Async Syntax | Sync Syntax |
|----------|---------|--------------|-------------|
| **Simple** | Async | `fn` | `sync fn` |
| JavaScript | Sync | `async function` | `function` |
| Python | Sync | `async def` | `def` |
| Rust | Sync | `async fn` | `fn` |
| Kotlin | Sync | `suspend fun` | `fun` |
| Go | Sync (goroutines) | `go func` | `func` |
| Zig | Sync | `async fn` | `fn` |

Simple's approach is unique: **async is the common case, sync is the exception**.

---

## Examples

### Web Server Handler

```simple
# Clean async-default style
fn handle_request(req: Request) -> Response:
    let user ~= authenticate(req)?
    let data ~= fetch_user_data(user.id)
    let rendered ~= render_template("user.html", data)
    return Response.ok(rendered)
```

### CLI Tool

```simple
# Mix of sync and async
fn main() -> i64:
    let args = parse_args()              # sync: no ~=
    let config ~= load_config(args.config_path)

    for file in args.files:
        let content ~= read_file(file)
        let result = process(content)    # sync: pure computation
        _ ~= write_file(file + ".out", result)

    return 0
```

### Library with Sync API

```simple
# Public sync API for simple use cases
pub sync fn hash(data: Bytes) -> Hash:
    return sha256_compute(data)

# Internal async for streaming
fn hash_stream(stream: Stream) -> Hash:
    let mut hasher = Sha256.new()
    for~ chunk in stream:
        hasher.update(chunk)
    return hasher.finalize()
```

### Actor Pattern

```simple
actor UserCache:
    state:
        cache: Dict[UserId, User] = {}

    # Handler is run-to-completion (like sync)
    on Get(id: UserId, reply_to: Pid[Option[User]]):
        send reply_to, self.cache.get(id)

    # Can spawn async tasks
    on Refresh(id: UserId):
        spawn_detached:
            let user ~= fetch_user_from_db(id)
            send self, Update(id, user)

    on Update(id: UserId, user: User):
        self.cache[id] = user
```

---

## Grammar Changes

### Function Declaration

```ebnf
FnDecl      -> FnModifiers "fn" Ident GenericParams? "(" Params? ")" RetType? ":" Block
FnModifiers -> ["pub"] ["sync"]

# Examples:
# fn foo() -> i64           -- async-capable (default)
# sync fn bar() -> i64      -- explicitly sync
# pub fn baz() -> str       -- public, async-capable
# pub sync fn qux() -> str  -- public, sync
```

### Sync Constraint in Types

```ebnf
FnType      -> ["sync"] "fn" "(" Types? ")" "->" Type

# Examples:
# fn(i64) -> i64            -- async-capable function type
# sync fn(i64) -> i64       -- sync function type
```

---

## Promise Type Details

### Core API

```simple
class Promise[T]:
    # Creation
    static fn new(executor: fn(resolve: fn(T), reject: fn(Error))) -> Promise[T]
    static fn resolve(value: T) -> Promise[T]
    static fn reject(error: Error) -> Promise[T]

    # Combinators (all return Promise)
    fn then[U](on_fulfilled: fn(T) -> U) -> Promise[U]
    fn catch(on_rejected: fn(Error) -> T) -> Promise[T]
    fn finally(on_settled: fn()) -> Promise[T]

    # Static combinators
    static fn all(promises: [Promise[T]]) -> Promise[[T]]
    static fn race(promises: [Promise[T]]) -> Promise[T]
    static fn any(promises: [Promise[T]]) -> Promise[T]
    static fn all_settled(promises: [Promise[T]]) -> Promise[[SettledResult[T]]]

    # Inspection (mainly for testing)
    fn is_pending() -> bool
    fn is_fulfilled() -> bool
    fn is_rejected() -> bool
```

### Interop with Result

```simple
# Promise + Result composition
fn fetch_or_error(url: Url) -> Promise[Result[Data, HttpError]]:
    return http.get(url)
        .then(\resp: parse_response(resp))
        .catch(\e: Err(HttpError.from(e)))

# With ~= and ?
fn use_it() -> Result[Data, Error]:
    let data ~= fetch_or_error(url)?
    return Ok(data)
```

---

## Error Handling

### Promise Rejection

```simple
fn might_fail() -> Data:
    if random() < 0.5:
        raise NetworkError("Connection lost")  # Rejects promise
    return Data.new()

fn caller():
    # ~= propagates rejection as exception
    let data ~= might_fail()   # May raise NetworkError

    # .catch() handles rejection
    let safe = might_fail()
        .catch(\e: default_data())
```

### Unhandled Rejection

```simple
# Global handler
Promise.on_unhandled_rejection(\e:
    log.error("Unhandled promise rejection: {e}")
)

# Or per-promise
let p = risky_operation()
    .catch(\e:
        log.warn("Operation failed: {e}")
        default_value()
    )
```

---

## Performance Considerations

### Sync Functions

- **No Promise allocation** - Direct return
- **No scheduler interaction** - Runs to completion
- **Inlinable** - Compiler can inline freely

### Async Functions

- **Promise allocation** - One per call (pooled)
- **Scheduler integration** - Cooperative yielding
- **Batching** - Multiple awaits can batch

### Optimization: Sync Inference

The compiler can optimize async functions that don't actually suspend:

```simple
fn technically_async() -> i64:
    return 42   # Never suspends

# Compiler may optimize to direct call (no Promise)
```

---

## Related Specifications

- [Suspension Operator](suspension_operator.md) - `~=`, `if~`, `while~` syntax
- [Concurrency](concurrency.md) - Actors, channels, threads
- [Functions](functions.md) - Base function syntax
- [Capability Effects](capability_effects.md) - Effect system
