# #47 Promise Type

**Status:** 📋 Planned
**Difficulty:** 3 (Medium)
**Implementation:** Rust
**Spec:** [async_default.md](../../spec/async_default.md#promise-type)

## Description

The `Promise[T]` type represents an async computation that will eventually produce a value of type `T`. Async functions implicitly return `Promise[T]`.

## Type Definition

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

## Implicit Wrapping

| Function Type | Declared Return | Actual Return |
|---------------|-----------------|---------------|
| Async `fn` | `T` | `Promise[T]` |
| Async `fn` | `Promise[T]` | `Promise[T]` (no double wrap) |
| `sync fn` | `T` | `T` (direct) |

## Combinators

```simple
# Chaining
fetch_data()
    .then(\d: transform(d))
    .catch(\e: handle_error(e))
    .finally(\: cleanup())

# Parallel
Promise.all([fetch_a(), fetch_b(), fetch_c()])
Promise.race([try_primary(), try_fallback()])
Promise.any([attempt1(), attempt2()])
Promise.all_settled([task1(), task2()])
```

## Core API

```simple
class Promise[T]:
    # Creation
    static fn resolve(value: T) -> Promise[T]
    static fn reject(error: Error) -> Promise[T]

    # Combinators
    fn then[U](on_fulfilled: fn(T) -> U) -> Promise[U]
    fn catch(on_rejected: fn(Error) -> T) -> Promise[T]
    fn finally(on_settled: fn()) -> Promise[T]

    # Static combinators
    static fn all(promises: [Promise[T]]) -> Promise[[T]]
    static fn race(promises: [Promise[T]]) -> Promise[T]
    static fn any(promises: [Promise[T]]) -> Promise[T]
    static fn all_settled(promises: [Promise[T]]) -> Promise[[SettledResult[T]]]

    # Inspection
    fn is_pending() -> bool
    fn is_fulfilled() -> bool
    fn is_rejected() -> bool
```

## Examples

```simple
# Get promise or await
let promise = fetch_user(id)     # promise: Promise[User]
let user ~= fetch_user(id)       # user: User (awaited)

# Chaining
let result = fetch_config()
    .then(\c: validate(c))
    .then(\c: apply(c))
    .catch(\e: default_config())

# Parallel fetch
let users ~= Promise.all([
    fetch_user(1_uid),
    fetch_user(2_uid),
    fetch_user(3_uid)
])
```

## Test Locations

- **Simple:** `simple/std_lib/test/features/concurrency/promise_type_spec.spl`
- **Rust:** `src/driver/tests/runner_async_tests.rs`

## Related Features

- #44 Async Default
- #45 Suspension Operator (~)
- #46 Effect Inference
- #43 Futures
