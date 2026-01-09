# #46 Effect Inference

**Status:** 🔄 Planning (Lean ✅)
**Difficulty:** 4 (Hard)
**Implementation:** Rust + Lean
**Spec:** [async_default.md](../../spec/async_default.md#effect-inference-automatic-asyncsync-detection)
**Plan:** [async_default_implementation.md](../../plans/async_default_implementation.md)

## Description

The compiler automatically infers whether a function is async or sync based on its body, eliminating the need for explicit annotations in most cases.

## Inference Rules

| Body Contains | Inferred Effect | Return Type |
|---------------|-----------------|-------------|
| `~=`, `if~`, `while~`, `for~` | async | `Promise[T]` |
| Calls to async functions | async | `Promise[T]` |
| Only sync operations | sync | `T` directly |

## Examples

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

# INFERRED AS ASYNC: calls async function
fn wrapper(id: UserId) -> User:
    return fetch_user(id)
# Compiler infers: fn wrapper(id: UserId) -> Promise[User]
```

## Type-Driven Await Inference

```simple
let p = fetch_user(id)       # p: Promise[User] (no await)
let u: User = fetch_user(id) # u: User (await inferred from type!)
let v ~= fetch_user(id)      # v: User (explicit await)
```

## Mutual Recursion

Fixed-point iteration handles mutually recursive functions:

```simple
fn ping(n: i64) -> i64:
    if n == 0: return 0
    return pong(n - 1)

fn pong(n: i64) -> i64:
    if n == 0: return 0
    return ping(n - 1)

# Both inferred as SYNC (no suspension in either)
```

## Lean 4 Verification

**Status:** ✅ Complete (265 lines, 10 theorems)

Formal properties verified in `AsyncEffectInference.lean`:

### Effect Inference (Theorems 1-5)
- **Effect Determinism**: Each function has exactly one inferred effect
- **Suspension Implies Async**: `~=` always makes function async
- **Sync Safety**: `sync fn` with suspension is a compile error
- **Effect Propagation**: Calling async fn makes caller async
- **Literals are Sync**: Constants never suspend

### Promise Type System (Theorems 6-10)
- **Async Returns Promise**: Async functions implicitly wrap return type in `Promise[T]`
- **Sync No Promise Wrap**: Sync functions return `T` directly
- **No Double-Wrap**: Explicit `Promise[T]` return prevents `Promise[Promise[T]]`
- **Await Inference Sound**: Type-driven await insertion is correct
- **Promise Unwrap Correct**: `Promise[T]` → `T` unwrapping is safe

**Models:**
- Type system with `Promise[T]`
- `transformReturnType: Effect × Type → Type`
- `shouldInsertAwait: Type × Type → Bool`
- `canUnwrapPromise: Type × Type → Bool`
- Fixed-point iteration for mutual recursion

## Test Locations

- **Simple:** `simple/std_lib/test/features/concurrency/effect_inference_spec.spl`
- **Rust:** `src/driver/tests/runner_async_tests.rs`
- **Lean:** `verification/type_inference_compile/src/AsyncEffectInference.lean`

## Related Features

- #44 Async Default
- #45 Suspension Operator (~)
- #47 Promise Type
