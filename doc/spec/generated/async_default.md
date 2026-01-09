# Async-Default Function Model

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/async_default_spec.spl`
> **Generated:** 2026-01-09 06:33:45
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
**Symbols:** Promise, Suspension, ExecutionMode, AsyncContext, Future
**Module:** simple_runtime::async
**Async by default:** No `async` keyword required
**Explicit suspension:** `~=` shows suspension points
**Sync when needed:** `sync fn` for synchronous code
**Type safety:** Promise types automatically inferred

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (31 tests)
- [Source Code](#source-code)

## Overview

This document specifies Simple's async-default execution model where functions are async by default and sync is explicit.

Functions without `sync` keyword return `Promise<T>` automatically. The suspension operator `~=` explicitly marks await points for readability and control.

## Related Specifications

- **Suspension Operator** - Explicit `~` suspension syntax
- **Concurrency** - Futures, actors, channels
- **Functions** - Function definitions
- **Type System** - Promise type inference

---

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `ASYNC` | [13](#double), [18](#async_ping) |
| `Actor` | [3](#load_data) |
| `Actual` | [1](#fetch_user) |
| `All` | [9](#try_all) |
| `Already` | [6](#get_cached_or_fetch) |
| `Assigning` | [14](#caller) |
| `Async` | [18](#async_ping), [31](#technically_async) |
| `AsyncPing` | [18](#async_ping) |
| `Both` | [17](#ping), [18](#async_ping) |
| `Cached` | [6](#get_cached_or_fetch) |
| `Caller` | [4](#caller), [14](#caller) |
| `Calls` | [17](#ping), [18](#async_ping) |
| `Can` | [20](#foo), [26](#examples_32) |
| `Cannot` | [3](#load_data) |
| `Compiler` | [13](#double), [16](#process), [31](#technically_async) |
| `Config` | [10](#example) |
| `Connection` | [29](#might_fail) |
| `Counter` | [3](#load_data) |
| `Data` | [3](#load_data), [4](#caller), [14](#caller), [16](#process), [19](#process), ... (7 total) |
| `Design` | [2](#design_overview_3) |
| `DesignOverview` | [2](#design_overview_3) |
| `Dict` | [26](#examples_32) |
| `Double` | [13](#double) |
| `Equivalent` | [14](#caller) |
| `Err` | [11](#unnamed_test), [28](#fetch_or_error) |
| `Error` | [5](#promise_type_6), [9](#try_all), [27](#unnamed_test), [28](#fetch_or_error), [30](#error_handling_36) |
| `ErrorHandling` | [30](#error_handling_36) |
| `Example` | [10](#example), [15](#example) |
| `Examples` | [26](#examples_32) |
| `ExecutionMode` | [2](#design_overview_3) |
| `Explicitly` | [3](#load_data) |
| `Fail` | [29](#might_fail) |
| `Fetch` | [1](#fetch_user), [6](#get_cached_or_fetch), [8](#parallel_fetch), [28](#fetch_or_error) |
| `FetchOrError` | [28](#fetch_or_error) |
| `FetchUser` | [1](#fetch_user) |
| `First` | [8](#parallel_fetch) |
| `Foo` | [20](#foo), [21](#foo), [22](#foo) |
| `Fulfilled` | [5](#promise_type_6), [9](#try_all) |
| `Get` | [6](#get_cached_or_fetch), [26](#examples_32) |
| `GetCachedOrFetch` | [6](#get_cached_or_fetch) |
| `Global` | [30](#error_handling_36) |
| `Handle` | [23](#handle_request) |
| `HandleRequest` | [23](#handle_request) |
| `Handler` | [26](#examples_32) |
| `Handling` | [30](#error_handling_36) |
| `Hash` | [25](#hash_stream) |
| `HashStream` | [25](#hash_stream) |
| `HttpError` | [28](#fetch_or_error) |
| `INFERRED` | [13](#double) |
| `Implicit` | [14](#caller) |
| `Increment` | [3](#load_data) |
| `Inspection` | [27](#unnamed_test) |
| `Item` | [13](#double) |
| `Links` | [2](#design_overview_3) |
| `Load` | [3](#load_data) |
| `LoadData` | [3](#load_data) |
| `Main` | [24](#main) |
| `May` | [29](#might_fail) |
| `Might` | [29](#might_fail) |
| `MightFail` | [29](#might_fail) |
| `NetworkError` | [29](#might_fail) |
| `Never` | [31](#technically_async) |
| `Non` | [4](#caller) |
| `Operation` | [30](#error_handling_36) |
| `Option` | [5](#promise_type_6), [26](#examples_32) |
| `Overview` | [2](#design_overview_3) |
| `Parallel` | [8](#parallel_fetch), [12](#unnamed_test) |
| `ParallelFetch` | [8](#parallel_fetch) |
| `Pending` | [5](#promise_type_6) |
| `Pid` | [26](#examples_32) |
| `Ping` | [17](#ping), [18](#async_ping) |
| `Pipeline` | [7](#process_pipeline) |
| `Process` | [7](#process_pipeline), [16](#process), [19](#process) |
| `ProcessPipeline` | [7](#process_pipeline) |
| `Promise` | [1](#fetch_user), [2](#design_overview_3), [4](#caller), [5](#promise_type_6), [6](#get_cached_or_fetch), ... (17 total) |
| `PromiseState` | [5](#promise_type_6) |
| `PromiseType` | [5](#promise_type_6) |
| `Refresh` | [26](#examples_32) |
| `Rejected` | [5](#promise_type_6), [9](#try_all) |
| `Rejects` | [29](#might_fail) |
| `Request` | [23](#handle_request) |
| `Response` | [8](#parallel_fetch), [23](#handle_request) |
| `Result` | [4](#caller), [7](#process_pipeline), [16](#process), [28](#fetch_or_error) |
| `Returns` | [6](#get_cached_or_fetch), [13](#double), [22](#foo) |
| `SYNC` | [13](#double), [17](#ping) |
| `SettledResult` | [9](#try_all), [27](#unnamed_test) |
| `Sha256` | [25](#hash_stream) |
| `Static` | [27](#unnamed_test) |
| `Stream` | [25](#hash_stream) |
| `Suspending` | [4](#caller) |
| `Suspension` | [2](#design_overview_3), [18](#async_ping) |
| `Sync` | [4](#caller), [10](#example) |
| `Task` | [9](#try_all) |
| `Technically` | [31](#technically_async) |
| `TechnicallyAsync` | [31](#technically_async) |
| `Try` | [9](#try_all) |
| `TryAll` | [9](#try_all) |
| `Type` | [5](#promise_type_6), [10](#example) |
| `Unhandled` | [30](#error_handling_36) |
| `Unnamed` | [11](#unnamed_test), [12](#unnamed_test), [27](#unnamed_test) |
| `Update` | [26](#examples_32) |
| `Url` | [8](#parallel_fetch), [28](#fetch_or_error) |
| `User` | [1](#fetch_user), [2](#design_overview_3), [6](#get_cached_or_fetch), [8](#parallel_fetch), [10](#example), ... (8 total) |
| `UserCache` | [26](#examples_32) |
| `UserId` | [1](#fetch_user), [6](#get_cached_or_fetch), [8](#parallel_fetch), [13](#double), [26](#examples_32) |
| `With` | [28](#fetch_or_error) |
| `Without` | [10](#example) |
| `all` | [8](#parallel_fetch), [9](#try_all), [27](#unnamed_test) |
| `all_settled` | [9](#try_all), [27](#unnamed_test) |
| `any` | [8](#parallel_fetch), [27](#unnamed_test) |
| `assert_compiles` | [2](#design_overview_3), [5](#promise_type_6), [26](#examples_32), [30](#error_handling_36) |
| `async` | [18](#async_ping), [31](#technically_async) |
| `async_ping` | [18](#async_ping) |
| `async_pong` | [18](#async_ping) |
| `authenticate` | [23](#handle_request) |
| `bar` | [20](#foo), [22](#foo) |
| `cached` | [6](#get_cached_or_fetch) |
| `call` | [31](#technically_async) |
| `caller` | [4](#caller), [14](#caller), [29](#might_fail) |
| `catch` | [7](#process_pipeline), [27](#unnamed_test), [28](#fetch_or_error), [29](#might_fail), [30](#error_handling_36) |
| `cleanup` | [7](#process_pipeline) |
| `completion` | [3](#load_data), [26](#examples_32) |
| `compute` | [3](#load_data), [4](#caller), [10](#example) |
| `compute_total` | [13](#double) |
| `data` | [3](#load_data) |
| `default_data` | [29](#might_fail) |
| `default_result` | [7](#process_pipeline) |
| `default_value` | [30](#error_handling_36) |
| `delay` | [18](#async_ping) |
| `design` | [2](#design_overview_3) |
| `design_overview` | [2](#design_overview_3) |
| `double` | [13](#double) |
| `error` | [28](#fetch_or_error), [30](#error_handling_36) |
| `error_handling` | [30](#error_handling_36) |
| `example` | [10](#example), [15](#example) |
| `examples` | [26](#examples_32) |
| `fail` | [29](#might_fail) |
| `fetch` | [1](#fetch_user), [6](#get_cached_or_fetch), [8](#parallel_fetch), [28](#fetch_or_error) |
| `fetch_data` | [7](#process_pipeline), [14](#caller), [19](#process) |
| `fetch_or_error` | [28](#fetch_or_error) |
| `fetch_user` | [1](#fetch_user), [2](#design_overview_3), [6](#get_cached_or_fetch), [8](#parallel_fetch), [10](#example), ... (7 total) |
| `fetch_user_data` | [23](#handle_request) |
| `fetch_user_from_db` | [26](#examples_32) |
| `finalize` | [25](#hash_stream) |
| `finally` | [7](#process_pipeline), [27](#unnamed_test) |
| `first_response` | [8](#parallel_fetch) |
| `first_success` | [8](#parallel_fetch) |
| `foo` | [20](#foo), [21](#foo), [22](#foo) |
| `from` | [28](#fetch_or_error) |
| `function` | [13](#double) |
| `get` | [6](#get_cached_or_fetch), [8](#parallel_fetch), [26](#examples_32), [28](#fetch_or_error) |
| `get_cached_or_fetch` | [6](#get_cached_or_fetch) |
| `get_promise` | [13](#double) |
| `get_user_name` | [13](#double) |
| `handle` | [23](#handle_request) |
| `handle_request` | [23](#handle_request) |
| `handling` | [30](#error_handling_36) |
| `hash` | [25](#hash_stream) |
| `hash_stream` | [25](#hash_stream) |
| `i64` | [4](#caller) |
| `is_fulfilled` | [27](#unnamed_test) |
| `is_pending` | [27](#unnamed_test) |
| `is_rejected` | [27](#unnamed_test) |
| `load` | [3](#load_data) |
| `load_config` | [10](#example), [24](#main) |
| `load_data` | [3](#load_data), [4](#caller) |
| `log_error` | [7](#process_pipeline) |
| `main` | [24](#main) |
| `map` | [8](#parallel_fetch), [9](#try_all), [13](#double) |
| `might` | [29](#might_fail) |
| `might_fail` | [29](#might_fail) |
| `new` | [25](#hash_stream), [29](#might_fail) |
| `on_unhandled_rejection` | [30](#error_handling_36) |
| `overview` | [2](#design_overview_3) |
| `parallel` | [8](#parallel_fetch) |
| `parallel_fetch` | [8](#parallel_fetch) |
| `parse` | [3](#load_data) |
| `parse_args` | [24](#main) |
| `parse_async` | [19](#process) |
| `parse_response` | [28](#fetch_or_error) |
| `ping` | [17](#ping), [18](#async_ping) |
| `pipeline` | [7](#process_pipeline) |
| `pong` | [17](#ping) |
| `process` | [7](#process_pipeline), [16](#process), [19](#process), [24](#main) |
| `process_pipeline` | [7](#process_pipeline) |
| `promise` | [5](#promise_type_6) |
| `promise_type` | [5](#promise_type_6) |
| `race` | [8](#parallel_fetch), [27](#unnamed_test) |
| `random` | [29](#might_fail) |
| `read_file` | [3](#load_data), [24](#main) |
| `render_template` | [23](#handle_request) |
| `request` | [23](#handle_request) |
| `resolve` | [6](#get_cached_or_fetch) |
| `risky_operation` | [30](#error_handling_36) |
| `run_task` | [9](#try_all) |
| `save` | [7](#process_pipeline) |
| `signature` | [1](#fetch_user) |
| `sleep` | [11](#unnamed_test) |
| `stream` | [25](#hash_stream) |
| `sum` | [13](#double) |
| `technically` | [31](#technically_async) |
| `technically_async` | [31](#technically_async) |
| `then` | [7](#process_pipeline), [28](#fetch_or_error) |
| `transform` | [7](#process_pipeline), [19](#process) |
| `try` | [9](#try_all) |
| `try_all` | [9](#try_all) |
| `type` | [5](#promise_type_6) |
| `unnamed` | [11](#unnamed_test), [12](#unnamed_test), [27](#unnamed_test) |
| `update` | [25](#hash_stream) |
| `use_it` | [28](#fetch_or_error) |
| `user` | [1](#fetch_user) |
| `warn` | [30](#error_handling_36) |
| `write_file` | [24](#main) |

---

## Test Cases (31 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [fetch_user](#fetch_user) | Motivation | `user`, `fetch`, `User` +7 |
| 2 | [design_overview_3](#design_overview_3) | Design Overview | `overview`, `Design`, `design` +10 |
| 3 | [load_data](#load_data) | Syntax | `load_data`, `load`, `Load` +12 |
| 4 | [caller](#caller) | Syntax | `caller`, `Caller`, `Non` +8 |
| 5 | [promise_type_6](#promise_type_6) | Promise Type | `promise_type`, `Type`, `promise` +10 |
| 6 | [get_cached_or_fetch](#get_cached_or_fetch) | Promise Type | `cached`, `get_cached_or_fetch`, `fetch` +12 |
| 7 | [process_pipeline](#process_pipeline) | Combinators (Promise Chaining) | `Process`, `ProcessPipeline`, `Pipeline` +14 |
| 8 | [parallel_fetch](#parallel_fetch) | Combinators (Promise Chaining) | `parallel_fetch`, `fetch`, `parallel` +17 |
| 9 | [try_all](#try_all) | Combinators (Promise Chaining) | `try_all`, `TryAll`, `All` +12 |
| 10 | [example](#example) | Sync Functions | `example`, `Example`, `Without` +8 |
| 11 | [unnamed_test](#unnamed_test) | Type Inference | `Unnamed`, `unnamed`, `sleep` +1 |
| 12 | [unnamed_test](#unnamed_test) | Type Inference | `Unnamed`, `unnamed`, `Parallel` |
| 13 | [double](#double) | Effect Inference (Automatic async/sync Detection) | `Double`, `double`, `Compiler` +15 |
| 14 | [caller](#caller) | Effect Inference (Automatic async/sync Detection) | `caller`, `Caller`, `Implicit` +5 |
| 15 | [example](#example) | Effect Inference (Automatic async/sync Detection) | `example`, `Example`, `User` +2 |
| 16 | [process](#process) | Effect Inference (Automatic async/sync Detection) | `Process`, `process`, `Compiler` +2 |
| 17 | [ping](#ping) | Effect Inference (Automatic async/sync Detection) | `Ping`, `ping`, `SYNC` +3 |
| 18 | [async_ping](#async_ping) | Effect Inference (Automatic async/sync Detection) | `async_ping`, `ping`, `Async` +9 |
| 19 | [process](#process) | Interaction with ~= Operator | `Process`, `process`, `transform` +3 |
| 20 | [foo](#foo) | Interaction with ~= Operator | `Foo`, `foo`, `bar` +1 |
| 21 | [foo](#foo) | Migration Strategy | `Foo`, `foo` |
| 22 | [foo](#foo) | Migration Strategy | `Foo`, `foo`, `Returns` +2 |
| 23 | [handle_request](#handle_request) | Examples | `handle`, `request`, `HandleRequest` +7 |
| 24 | [main](#main) | Examples | `Main`, `main`, `load_config` +4 |
| 25 | [hash_stream](#hash_stream) | Examples | `hash_stream`, `HashStream`, `Hash` +7 |
| 26 | [examples_32](#examples_32) | Examples | `Examples`, `examples`, `completion` +14 |
| 27 | [unnamed_test](#unnamed_test) | Promise Type Details | `Unnamed`, `unnamed`, `catch` +13 |
| 28 | [fetch_or_error](#fetch_or_error) | Promise Type Details | `fetch`, `Error`, `Fetch` +16 |
| 29 | [might_fail](#might_fail) | Error Handling | `Might`, `might_fail`, `might` +13 |
| 30 | [error_handling_36](#error_handling_36) | Error Handling | `error_handling`, `ErrorHandling`, `Error` +13 |
| 31 | [technically_async](#technically_async) | Performance Considerations | `async`, `Async`, `technically` +7 |

---

### Test 1: Motivation {#fetch_user}

**Test name:** `fetch_user`

**Linked Symbols:**
- `user`
- `fetch`
- `User`
- `Fetch`
- `FetchUser`
- `fetch_user`
- `signature`
- `UserId`
- `Actual`
- `Promise`

**Code:**

```simple
fn fetch_user(id: UserId) -> User

# Actual signature (implicit)
fn fetch_user(id: UserId) -> Promise[User]
```

### Test 2: Design Overview {#design_overview_3}

**Test name:** `design_overview_3`

**Linked Symbols:**
- `overview`
- `Design`
- `design`
- `DesignOverview`
- `design_overview`
- `Overview`
- `Links`
- `User`
- `ExecutionMode`
- `Suspension`
- ... and 3 more

**Code:**

```simple
test "design_overview_3":
    """
    Suspension operator unwraps Promise to underlying type.
    
    **Links:** Promise, Suspension::operator, ExecutionMode
    """
    let user ~= fetch_user(1_uid)   # user: User (not Promise[User])
    assert_compiles()
```

### Test 3: Syntax {#load_data}

**Test name:** `load_data`

**Linked Symbols:**
- `load_data`
- `load`
- `Load`
- `data`
- `LoadData`
- `Data`
- `parse`
- `Increment`
- `compute`
- `Actor`
- ... and 5 more

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

### Test 4: Syntax {#caller}

**Test name:** `caller`

**Linked Symbols:**
- `caller`
- `Caller`
- `Non`
- `Result`
- `i64`
- `compute`
- `load_data`
- `Sync`
- `Suspending`
- `Promise`
- ... and 1 more

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

### Test 5: Promise Type {#promise_type_6}

**Test name:** `promise_type_6`

**Linked Symbols:**
- `promise_type`
- `Type`
- `promise`
- `PromiseType`
- `Promise`
- `type`
- `Rejected`
- `PromiseState`
- `Error`
- `assert_compiles`
- ... and 3 more

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

### Test 6: Promise Type {#get_cached_or_fetch}

**Test name:** `get_cached_or_fetch`

**Linked Symbols:**
- `cached`
- `get_cached_or_fetch`
- `fetch`
- `get`
- `Fetch`
- `Cached`
- `GetCachedOrFetch`
- `Get`
- `Returns`
- `resolve`
- ... and 5 more

**Code:**

```simple
fn get_cached_or_fetch(id: UserId) -> Promise[User]:
    if let Some(user) = cache.get(id):
        return Promise.resolve(user)   # Already resolved
    return fetch_user(id)              # Returns Promise[User]
```

### Test 7: Combinators (Promise Chaining) {#process_pipeline}

**Test name:** `process_pipeline`

**Linked Symbols:**
- `Process`
- `ProcessPipeline`
- `Pipeline`
- `process_pipeline`
- `pipeline`
- `process`
- `catch`
- `transform`
- `cleanup`
- `Result`
- ... and 7 more

**Code:**

```simple
fn process_pipeline() -> Promise[Result]:
    return fetch_data()
        .then(\data: transform(data))
        .then(\transformed: save(transformed))
        .catch(\err: log_error(err); default_result())
        .finally(\: cleanup())
```

### Test 8: Combinators (Promise Chaining) {#parallel_fetch}

**Test name:** `parallel_fetch`

**Linked Symbols:**
- `parallel_fetch`
- `fetch`
- `parallel`
- `Fetch`
- `Parallel`
- `ParallelFetch`
- `first_response`
- `map`
- `Response`
- `User`
- ... and 10 more

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

### Test 9: Combinators (Promise Chaining) {#try_all}

**Test name:** `try_all`

**Linked Symbols:**
- `try_all`
- `TryAll`
- `All`
- `Try`
- `try`
- `all`
- `Task`
- `Rejected`
- `SettledResult`
- `map`
- ... and 5 more

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

### Test 10: Sync Functions {#example}

**Test name:** `example`

**Linked Symbols:**
- `example`
- `Example`
- `Without`
- `Config`
- `User`
- `Type`
- `compute`
- `load_config`
- `Sync`
- `Promise`
- ... and 1 more

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

### Test 11: Type Inference {#unnamed_test}

**Test name:** `unnamed_test`

**Linked Symbols:**
- `Unnamed`
- `unnamed`
- `sleep`
- `Err`

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

### Test 12: Type Inference {#unnamed_test}

**Test name:** `unnamed_test`

**Linked Symbols:**
- `Unnamed`
- `unnamed`
- `Parallel`

**Code:**

```simple
fn map_async[T, U](items: [T], f: fn(T) -> U) -> [U]:
    return [f(item) ~= for item in items]  # Parallel await
```

### Test 13: Effect Inference (Automatic async/sync Detection) {#double}

**Test name:** `double`

**Linked Symbols:**
- `Double`
- `double`
- `Compiler`
- `Returns`
- `get_promise`
- `map`
- `User`
- `fetch_user`
- `UserId`
- `SYNC`
- ... and 8 more

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

### Test 14: Effect Inference (Automatic async/sync Detection) {#caller}

**Test name:** `caller`

**Linked Symbols:**
- `caller`
- `Caller`
- `Implicit`
- `Equivalent`
- `Promise`
- `fetch_data`
- `Assigning`
- `Data`

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

### Test 15: Effect Inference (Automatic async/sync Detection) {#example}

**Test name:** `example`

**Linked Symbols:**
- `example`
- `Example`
- `User`
- `Promise`
- `fetch_user`

**Code:**

```simple
fn example():
    let p = fetch_user(id)      # p: Promise[User] (no await)
    let u: User = fetch_user(id) # u: User (await inferred from type)
    let v ~= fetch_user(id)      # v: User (explicit await)
```

### Test 16: Effect Inference (Automatic async/sync Detection) {#process}

**Test name:** `process`

**Linked Symbols:**
- `Process`
- `process`
- `Compiler`
- `Data`
- `Result`

**Code:**

```simple
fn process(data: Data) -> Result:
    ...  # Compiler figures it out
```

### Test 17: Effect Inference (Automatic async/sync Detection) {#ping}

**Test name:** `ping`

**Linked Symbols:**
- `Ping`
- `ping`
- `SYNC`
- `Both`
- `Calls`
- `pong`

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

### Test 18: Effect Inference (Automatic async/sync Detection) {#async_ping}

**Test name:** `async_ping`

**Linked Symbols:**
- `async_ping`
- `ping`
- `Async`
- `async`
- `Ping`
- `AsyncPing`
- `Suspension`
- `ASYNC`
- `Both`
- `async_pong`
- ... and 2 more

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

### Test 19: Interaction with ~= Operator {#process}

**Test name:** `process`

**Linked Symbols:**
- `Process`
- `process`
- `transform`
- `fetch_data`
- `parse_async`
- `Data`

**Code:**

```simple
fn process() -> Data:
    # ~= is the standard way to call and await
    let raw ~= fetch_data()
    let parsed ~= parse_async(raw)
    return transform(parsed)
```

### Test 20: Interaction with ~= Operator {#foo}

**Test name:** `foo`

**Linked Symbols:**
- `Foo`
- `foo`
- `bar`
- `Can`

**Code:**

```simple
fn foo() -> i64:
    return 42

# Can now mark sync explicitly
sync fn bar() -> i64:
    return 42
```

### Test 21: Migration Strategy {#foo}

**Test name:** `foo`

**Linked Symbols:**
- `Foo`
- `foo`

**Code:**

```simple
fn foo() -> i64:
    return 42

# No warning
sync fn foo() -> i64:
    return 42
```

### Test 22: Migration Strategy {#foo}

**Test name:** `foo`

**Linked Symbols:**
- `Foo`
- `foo`
- `Returns`
- `bar`
- `Promise`

**Code:**

```simple
fn foo() -> i64:         # Returns Promise[i64]
    return 42

sync fn bar() -> i64:    # Returns i64 directly
    return 42
```

### Test 23: Examples {#handle_request}

**Test name:** `handle_request`

**Linked Symbols:**
- `handle`
- `request`
- `HandleRequest`
- `Request`
- `handle_request`
- `Handle`
- `authenticate`
- `Response`
- `render_template`
- `fetch_user_data`

**Code:**

```simple
fn handle_request(req: Request) -> Response:
    let user ~= authenticate(req)?
    let data ~= fetch_user_data(user.id)
    let rendered ~= render_template("user.html", data)
    return Response.ok(rendered)
```

### Test 24: Examples {#main}

**Test name:** `main`

**Linked Symbols:**
- `Main`
- `main`
- `load_config`
- `read_file`
- `write_file`
- `parse_args`
- `process`

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

### Test 25: Examples {#hash_stream}

**Test name:** `hash_stream`

**Linked Symbols:**
- `hash_stream`
- `HashStream`
- `Hash`
- `hash`
- `stream`
- `Stream`
- `Sha256`
- `update`
- `finalize`
- `new`

**Code:**

```simple
fn hash_stream(stream: Stream) -> Hash:
    let mut hasher = Sha256.new()
    for~ chunk in stream:
        hasher.update(chunk)
    return hasher.finalize()
```

### Test 26: Examples {#examples_32}

**Test name:** `examples_32`

**Linked Symbols:**
- `Examples`
- `examples`
- `completion`
- `UserCache`
- `Refresh`
- `User`
- `Update`
- `fetch_user_from_db`
- `UserId`
- `Handler`
- ... and 7 more

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

### Test 27: Promise Type Details {#unnamed_test}

**Test name:** `unnamed_test`

**Linked Symbols:**
- `Unnamed`
- `unnamed`
- `catch`
- `SettledResult`
- `Static`
- `is_pending`
- `Inspection`
- `race`
- `any`
- `Error`
- ... and 6 more

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

### Test 28: Promise Type Details {#fetch_or_error}

**Test name:** `fetch_or_error`

**Linked Symbols:**
- `fetch`
- `Error`
- `Fetch`
- `error`
- `FetchOrError`
- `fetch_or_error`
- `catch`
- `Result`
- `HttpError`
- `Url`
- ... and 9 more

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

### Test 29: Error Handling {#might_fail}

**Test name:** `might_fail`

**Linked Symbols:**
- `Might`
- `might_fail`
- `might`
- `fail`
- `Fail`
- `MightFail`
- `caller`
- `catch`
- `default_data`
- `May`
- ... and 6 more

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

### Test 30: Error Handling {#error_handling_36}

**Test name:** `error_handling_36`

**Linked Symbols:**
- `error_handling`
- `ErrorHandling`
- `Error`
- `handling`
- `error`
- `Handling`
- `Global`
- `catch`
- `Operation`
- `risky_operation`
- ... and 6 more

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

### Test 31: Performance Considerations {#technically_async}

**Test name:** `technically_async`

**Linked Symbols:**
- `async`
- `Async`
- `technically`
- `TechnicallyAsync`
- `technically_async`
- `Technically`
- `Compiler`
- `Never`
- `call`
- `Promise`

**Code:**

```simple
fn technically_async() -> i64:
    return 42   # Never suspends

# Compiler may optimize to direct call (no Promise)
```

---

## Source Code

**View full specification:** [async_default_spec.spl](../../tests/specs/async_default_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/async_default_spec.spl`*
