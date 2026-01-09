# Async-Default Function Model

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/async_default_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/async_default_spec.spl
> ```

**Status:** Draft
**Feature IDs:** #276-285
**Keywords:** async, sync, effects, promises, futures
**Last Updated:** 2026-01-05
**Topics:** concurrency, syntax, effects

## Overview

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

## Related Specifications

- **Suspension Operator** - Explicit `~` suspension syntax
- **Concurrency** - Futures, actors, channels
- **Functions** - Function definitions

---

## Test Cases (31 total)

| Test | Section | Description |
|------|---------|-------------|
| [fetch_user](#test-1) | Motivation |  |
| [design_overview_3](#test-2) | Design Overview |  |
| [load_data](#test-3) | Syntax |  |
| [caller](#test-4) | Syntax |  |
| [promise_type_6](#test-5) | Promise Type |  |
| [get_cached_or_fetch](#test-6) | Promise Type |  |
| [process_pipeline](#test-7) | Combinators (Promise Chaining) |  |
| [parallel_fetch](#test-8) | Combinators (Promise Chaining) |  |
| [try_all](#test-9) | Combinators (Promise Chaining) |  |
| [example](#test-10) | Sync Functions |  |
| [unnamed_test](#test-11) | Type Inference |  |
| [unnamed_test](#test-12) | Type Inference |  |
| [double](#test-13) | Effect Inference (Automatic async/sync Detection) |  |
| [caller](#test-14) | Effect Inference (Automatic async/sync Detection) |  |
| [example](#test-15) | Effect Inference (Automatic async/sync Detection) |  |
| [process](#test-16) | Effect Inference (Automatic async/sync Detection) |  |
| [ping](#test-17) | Effect Inference (Automatic async/sync Detection) |  |
| [async_ping](#test-18) | Effect Inference (Automatic async/sync Detection) |  |
| [process](#test-19) | Interaction with ~= Operator |  |
| [foo](#test-20) | Interaction with ~= Operator |  |
| [foo](#test-21) | Migration Strategy |  |
| [foo](#test-22) | Migration Strategy |  |
| [handle_request](#test-23) | Examples |  |
| [main](#test-24) | Examples |  |
| [hash_stream](#test-25) | Examples |  |
| [examples_32](#test-26) | Examples |  |
| [unnamed_test](#test-27) | Promise Type Details |  |
| [fetch_or_error](#test-28) | Promise Type Details |  |
| [might_fail](#test-29) | Error Handling |  |
| [error_handling_36](#test-30) | Error Handling |  |
| [technically_async](#test-31) | Performance Considerations |  |

---

### Test 1: Motivation

**Test name:** `fetch_user`

**Code:**

```simple
fn fetch_user(id: UserId) -> User

# Actual signature (implicit)
fn fetch_user(id: UserId) -> Promise[User]
```

### Test 2: Design Overview

**Test name:** `design_overview_3`

**Code:**

```simple
test "design_overview_3":
    """
    Design Overview
    """
    let user ~= fetch_user(1_uid)   # user: User (not Promise[User])
    assert_compiles()
```

### Test 3: Syntax

**Test name:** `load_data`

**Code:**

```simple
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

### Test 4: Syntax

**Test name:** `caller`

**Code:**

```simple
fn caller() -> Result:
    # Suspending call - awaits and unwraps
    let data ~= load_data()           # data: Data

    # Non-suspending call - gets the Promise
    let promise = load_data()          # promise: Promise[Data]

    # Sync function - no promise wrapping
    let result = compute(42)           # result: i64 (direct)
```

### Test 5: Promise Type

**Test name:** `promise_type_6`

**Code:**

```simple
test "promise_type_6":
    """
    Promise Type
    """
    enum PromiseState:
        Pending
        Fulfilled
        Rejected

    class Promise[T]:
        state: PromiseState
        value: Option[T]
        error: Option[Error]
    assert_compiles()
```

### Test 6: Promise Type

**Test name:** `get_cached_or_fetch`

**Code:**

```simple
fn get_cached_or_fetch(id: UserId) -> Promise[User]:
    if let Some(user) = cache.get(id):
        return Promise.resolve(user)   # Already resolved
    return fetch_user(id)              # Returns Promise[User]
```

### Test 7: Combinators (Promise Chaining)

**Test name:** `process_pipeline`

**Code:**

```simple
fn process_pipeline() -> Promise[Result]:
    return fetch_data()
        .then(\data: transform(data))
        .then(\transformed: save(transformed))
        .catch(\err: log_error(err); default_result())
        .finally(\: cleanup())
```

### Test 8: Combinators (Promise Chaining)

**Test name:** `parallel_fetch`

**Code:**

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

### Test 9: Combinators (Promise Chaining)

**Test name:** `try_all`

**Code:**

```simple
fn try_all(tasks: [Task]) -> Promise[[SettledResult[T]]]:
    let promises = tasks.map(\t: run_task(t))
    return Promise.all_settled(promises)

# SettledResult is:
enum SettledResult[T]:
    Fulfilled(value: T)
    Rejected(error: Error)
```

### Test 10: Sync Functions

**Test name:** `example`

**Code:**

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

### Test 11: Type Inference

**Test name:** `unnamed_test`

**Code:**

```simple
fn retry[T](f: fn() -> T, attempts: i64) -> T:
    for i in 0..attempts:
        match f():
            case Ok(v): return v
            case Err(e) if i < attempts - 1:
                _ ~= timer.sleep(1000_ms)
            case Err(e):
                return Err(e)
```

### Test 12: Type Inference

**Test name:** `unnamed_test`

**Code:**

```simple
fn map_async[T, U](items: [T], f: fn(T) -> U) -> [U]:
    return [f(item) ~= for item in items]  # Parallel await
```

### Test 13: Effect Inference (Automatic async/sync Detection)

**Test name:** `double`

**Code:**

```simple
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

### Test 14: Effect Inference (Automatic async/sync Detection)

**Test name:** `caller`

**Code:**

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

### Test 15: Effect Inference (Automatic async/sync Detection)

**Test name:** `example`

**Code:**

```simple
fn example():
    let p = fetch_user(id)      # p: Promise[User] (no await)
    let u: User = fetch_user(id) # u: User (await inferred from type)
    let v ~= fetch_user(id)      # v: User (explicit await)
```

### Test 16: Effect Inference (Automatic async/sync Detection)

**Test name:** `process`

**Code:**

```simple
fn process(data: Data) -> Result:
    ...  # Compiler figures it out
```

### Test 17: Effect Inference (Automatic async/sync Detection)

**Test name:** `ping`

**Code:**

```simple
fn ping(n: i64) -> i64:
    if n == 0: return 0
    return pong(n - 1)        # Calls pong

fn pong(n: i64) -> i64:
    if n == 0: return 0
    return ping(n - 1)        # Calls ping

# Both inferred as SYNC (no suspension in either)
```

### Test 18: Effect Inference (Automatic async/sync Detection)

**Test name:** `async_ping`

**Code:**

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

### Test 19: Interaction with ~= Operator

**Test name:** `process`

**Code:**

```simple
fn process() -> Data:
    # ~= is the standard way to call and await
    let raw ~= fetch_data()
    let parsed ~= parse_async(raw)
    return transform(parsed)
```

### Test 20: Interaction with ~= Operator

**Test name:** `foo`

**Code:**

```simple
fn foo() -> i64:
    return 42

# Can now mark sync explicitly
sync fn bar() -> i64:
    return 42
```

### Test 21: Migration Strategy

**Test name:** `foo`

**Code:**

```simple
fn foo() -> i64:
    return 42

# No warning
sync fn foo() -> i64:
    return 42
```

### Test 22: Migration Strategy

**Test name:** `foo`

**Code:**

```simple
fn foo() -> i64:         # Returns Promise[i64]
    return 42

sync fn bar() -> i64:    # Returns i64 directly
    return 42
```

### Test 23: Examples

**Test name:** `handle_request`

**Code:**

```simple
fn handle_request(req: Request) -> Response:
    let user ~= authenticate(req)?
    let data ~= fetch_user_data(user.id)
    let rendered ~= render_template("user.html", data)
    return Response.ok(rendered)
```

### Test 24: Examples

**Test name:** `main`

**Code:**

```simple
fn main() -> i64:
    let args = parse_args()              # sync: no ~=
    let config ~= load_config(args.config_path)

    for file in args.files:
        let content ~= read_file(file)
        let result = process(content)    # sync: pure computation
        _ ~= write_file(file + ".out", result)

    return 0
```

### Test 25: Examples

**Test name:** `hash_stream`

**Code:**

```simple
fn hash_stream(stream: Stream) -> Hash:
    let mut hasher = Sha256.new()
    for~ chunk in stream:
        hasher.update(chunk)
    return hasher.finalize()
```

### Test 26: Examples

**Test name:** `examples_32`

**Code:**

```simple
test "examples_32":
    """
    Examples
    """
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
    assert_compiles()
```

### Test 27: Promise Type Details

**Test name:** `unnamed_test`

**Code:**

```simple
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

### Test 28: Promise Type Details

**Test name:** `fetch_or_error`

**Code:**

```simple
fn fetch_or_error(url: Url) -> Promise[Result[Data, HttpError]]:
    return http.get(url)
        .then(\resp: parse_response(resp))
        .catch(\e: Err(HttpError.from(e)))

# With ~= and ?
fn use_it() -> Result[Data, Error]:
    let data ~= fetch_or_error(url)?
    return Ok(data)
```

### Test 29: Error Handling

**Test name:** `might_fail`

**Code:**

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

### Test 30: Error Handling

**Test name:** `error_handling_36`

**Code:**

```simple
test "error_handling_36":
    """
    Error Handling
    """
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
    assert_compiles()
```

### Test 31: Performance Considerations

**Test name:** `technically_async`

**Code:**

```simple
fn technically_async() -> i64:
    return 42   # Never suspends

# Compiler may optimize to direct call (no Promise)
```

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/async_default_spec.spl`*
