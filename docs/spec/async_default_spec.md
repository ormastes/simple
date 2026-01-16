# Async-by-Default Functions

*Source: `simple/std_lib/test/features/concurrency/async_default_spec.spl`*

---

# Async-by-Default Functions

**Feature ID:** #44
**Category:** Concurrency
**Difficulty:** 3/5
**Status:** 🚧 Planned (Not Yet Implemented)

## Overview

Simple adopts an **async-by-default** concurrency model where all functions are implicitly
asynchronous unless explicitly marked with the `sync` keyword. This design decision inverts
the traditional model (where functions are sync by default and `async` must be added) to
better support modern I/O-bound applications and cloud-native workloads.

The async-by-default approach means:
    - Functions can suspend execution to wait for I/O without blocking threads
- The compiler automatically infers whether a function actually needs async capability
- Functions that don't perform suspension are optimized to run synchronously
- Explicit `sync` keyword is available for functions that must never suspend

This model is inspired by languages like Zig (which has similar colorblind concurrency) while
maintaining Simple's goal of being easy to learn and safe by default.

## Key Features

- **Async by Default:** All `fn` declarations are async-capable
- **Automatic Inference:** Compiler detects when functions can run synchronously
- **Explicit Sync:** `sync fn` keyword for guaranteed synchronous execution
- **Effect Checking:** Compiler prevents sync functions from calling async code
- **Zero-Cost Abstraction:** Sync-inferred functions have no async runtime overhead
- **Promise Wrapping:** Async functions return `Promise<T>` transparently

## Syntax

**Async-Capable Function (Default):**
```simple
fn fetch_user(id: UserId) -> User:
    val resp ~= http.get("/users/{id}")  # ~= is suspension operator
    return parse(resp)
# Actual return type: Promise<User>
```

**Explicitly Synchronous Function:**
```simple
sync fn compute(x: i64) -> i64:
    return x * x
# Guaranteed to never suspend, return type: i64
```

**Inferred as Sync:**
```simple
fn double(x: i64) -> i64:
    return x * 2
# No suspension operators, compiler infers sync behavior
# Optimized to run without async overhead
```

## Motivation & Design

### Why Async-by-Default?

**Traditional async/await suffers from "function coloring":**
- Sync functions can't call async functions
- Async functions can call sync functions
- This creates two separate function "colors" that don't compose well
- Refactoring sync code to async requires changing all callers

**Simple's async-by-default solves this:**
- All functions are async-capable, but many run synchronously
- Sync-inferred functions have zero overhead
- Refactoring is simpler: adding suspension doesn't break callers
- Only truly synchronous critical paths need `sync fn`

### Comparison with Other Languages

| Language | Model | Annotation | Inference |
|----------|-------|------------|-----------|
| **Simple** | Async-default | `sync fn` for sync | ✅ Yes |
| JavaScript | Async explicit | `async function` | ❌ No |
| Rust | Async explicit | `async fn` | ❌ No |
| Python | Async explicit | `async def` | ❌ No |
| Zig | Colored-blind | No keywords | ✅ Yes |
| Go | Goroutines | Implicit concurrency | N/A |

### Effect System

Simple uses an **effect type system** to track suspension:

```
Effect = Sync | Async

fn declaration    → Async effect (may suspend)
sync fn declaration → Sync effect (never suspends)

Function calls inherit effects:
    - Sync function calls async function → Compile error
- Async function calls sync function → OK
- Async function calls async function → OK
```

This ensures that:
    - Performance-critical code marked `sync fn` cannot accidentally suspend
- Async code can freely call sync utilities
- Effect pollution is prevented at compile time

## Test Coverage (Planned)

This specification validates the following when implemented:

1. **Async-by-Default:** Functions declared with `fn` are async-capable
2. **Sync Inference:** Pure computation functions run synchronously
3. **Explicit Sync:** `sync fn` keyword marks guaranteed synchronous functions
4. **Sync Validation:** Compiler rejects suspension in `sync fn`
5. **Promise Wrapping:** Async functions return `Promise<T>` transparently
6. **Effect Propagation:** Sync functions cannot call async functions

## Implementation

**Status:** 🚧 **Planned** - Not yet implemented

**Primary Files (Planned):**
- `src/compiler/src/effects.rs` - Effect inference and checking
- `src/parser/src/statements/mod.rs` - `sync fn` keyword parsing
- `src/runtime/src/promise.rs` - Promise type implementation

**Testing (Future):**
- `src/driver/tests/runner_async_tests.rs` - Async execution tests

**Dependencies:**
- Feature #41: Concurrency Primitives (Promise, Future)
- Feature #45: Suspension Operator (`~=`)
- Feature #46: Effect Inference System

**Required By:**
- None yet (foundational concurrency feature)

## Effect Inference Algorithm (Planned)

**Inference Rules:**

```
1. Function contains suspension operator (~=)     → Async
2. Function calls another async function          → Async
3. Function declared with 'sync fn'               → Sync (enforced)
4. Function has no suspensions or async calls     → Sync (inferred)
```

**Example Inference:**

```simple
# Case 1: Explicit suspension → Async
fn fetch_data():
    val result ~= http.get("/api/data")
    return result
# Effect: Async (contains ~= operator)

# Case 2: Calls async function → Async
fn process():
    val data = fetch_data()  # fetch_data is async
    return transform(data)
# Effect: Async (calls async function)

# Case 3: Explicit sync → Sync (enforced)
sync fn compute(x: i64) -> i64:
    return x * x
# Effect: Sync (enforced by keyword)

# Case 4: Pure computation → Sync (inferred)
fn add(a: i64, b: i64) -> i64:
    return a + b
# Effect: Sync (inferred, no suspensions)
```

## Promise Type System (Planned)

**Type Transformation:**

```
Declared signature:       fn f() -> T
Actual return type:       Promise<T>  (if async)
                          T            (if sync-inferred)

User writes:    fn fetch() -> User
Compiler sees:  fn fetch() -> Promise<User>
```

**Promise Unwrapping:**

```simple
# Using suspension operator
val user: User = fetch()~  # Short form
val user: User ~= fetch()  # Infix form

# Both desugar to:
    val promise: Promise<User> = fetch()
val user: User = await(promise)
```

## Error Messages (Planned)

**Sync calling async:**
```
error: sync function cannot call async function
  --> src/main.spl:5:12
   |
 5 |     val x = fetch_data()
   |             ^^^^^^^^^^^^ async function
   |
note: declared as sync here
  --> src/main.spl:3:1
   |
 3 | sync fn process():
   | ^^^^^^^^^^^^^^^^^ this function is sync
   |
help: remove 'sync' keyword or use suspension operator
   |
 5 |     val x ~= fetch_data()
   |           ++
```

**Suspension in sync function:**
```
error: suspension operator not allowed in sync function
  --> src/main.spl:6:12
   |
 6 |     val x ~= http.get("/api")
   |            ^^ suspension operator
   |
note: declared as sync here
  --> src/main.spl:4:1
   |
 4 | sync fn fetch():
   | ^^^^^^^^^^^^^^^^ this function cannot suspend
```

## Performance Characteristics (Planned)

| Function Type | Overhead | Use Case |
|---------------|----------|----------|
| Sync-inferred | Zero | Pure computations, hot loops |
| Async (with suspension) | ~100ns | I/O operations, network calls |
| Sync (explicit) | Zero | Critical paths, low-latency code |

**Optimization:**

Sync-inferred functions compile to the same machine code as traditional
synchronous functions with no async runtime overhead.

```rust
// Simple code:
    fn add(a: i64, b: i64) -> i64:
        return a + b

// Compiles to (equivalent Rust):
    fn add(a: i64, b: i64) -> i64 {
    a + b  // No async machinery
}
```

## Related Features

- Feature #41: Concurrency Primitives (Promise, Future, async runtime)
- Feature #45: Suspension Operator (`~=` for await/suspend)
- Feature #46: Effect Inference System (tracks sync/async)
- Feature #47: Structured Concurrency (spawn, cancel, nursery)
- Feature #48: Actor Model (message-passing concurrency)

## Examples (Future Usage)

**Web Server Handler:**
```simple
fn handle_request(req: Request) -> Response:
    val user_id = req.headers['user-id']
    val user ~= database.get_user(user_id)
    val posts ~= database.get_posts(user.id)
    return render_template('profile', user, posts)
# Async: contains suspension operators
```

**Pure Business Logic:**
```simple
fn calculate_discount(price: f64, tier: Tier) -> f64:
    match tier:
        Tier::Bronze -> price * 0.05
        Tier::Silver -> price * 0.10
        Tier::Gold -> price * 0.15
# Sync-inferred: no suspension or I/O
```

**Performance-Critical Path:**
```simple
sync fn hash_password(password: text) -> Hash:
    # CPU-intensive, must not suspend
    return argon2.hash(password)
# Explicit sync: guaranteed no suspension
```

**Concurrent Batch Processing:**
```simple
fn process_batch(items: List<Item>) -> List<Result>:
    val tasks = items.map(|item| async {
        val enriched ~= enrich(item)
        val validated ~= validate(enriched)
        return transform(validated)
    })
    val results ~= Promise.all(tasks)
    return results
# Async: spawns concurrent tasks
```

## Migration Notes

**When This Feature is Implemented:**

Existing synchronous code will:
    1. Continue to work (inferred as sync)
2. Gain the ability to call async code without refactoring
3. Benefit from zero-cost sync inference

Breaking changes:
    - Functions that currently block on I/O should use suspension operator
- Performance-critical paths should add `sync fn` annotation

**Migration Path:**
```simple
# Before (blocking I/O)
fn old_fetch():
    return blocking_http_get("/api")

# After (async with suspension)
fn new_fetch():
    return http.get("/api")~
```

**Timeline:**
- **Phase 1:** Implement Promise type and suspension operator (#41, #45)
- **Phase 2:** Implement effect inference system (#46)
- **Phase 3:** Enable async-by-default with sync keyword (this feature)
- **Phase 4:** Migrate stdlib to use async I/O

**Current Status:**
- ⏳ Awaiting Promise type implementation
- ⏳ Awaiting suspension operator (`~=`) implementation
- ⏳ Awaiting effect inference system

**Estimated Completion:** Not scheduled

---

**Notes:**
- All tests in this specification are currently **skipped**
- Tests will be enabled when dependencies (#41, #45, #46) are complete
- This spec serves as design documentation for the planned feature

**Migration Notes (This File):**
- Automated migration: N/A (planned feature spec)
- Documentation enhancement: ~48 minutes (Session 4)
- Tests remain skipped until feature implementation

## Async-by-Default Function Semantics

    In Simple's concurrency model, all functions declared with `fn` are async-capable
    by default. This means they can use the suspension operator (`~=`) to yield control
    while waiting for I/O operations, network requests, or other asynchronous work.

    **Design Philosophy:**
    - Modern applications are I/O-bound, not CPU-bound
    - Async should be the default, not the exception
    - Sync inference optimizes pure computation automatically
    - Explicit `sync fn` available for critical paths

    **Key Characteristics:**
    - Functions can suspend execution without blocking OS threads
    - Compiler infers when functions can run synchronously
    - No performance penalty for sync-inferred functions
    - Effect system prevents accidental blocking in async contexts

    **Syntax:**
    ```simple
    # Async-capable (default)
    fn fetch_user(id: UserId) -> User:
        val resp ~= http.get("/users/{id}")
        return parse(resp)

    # Explicitly synchronous
    sync fn hash_password(pwd: text) -> Hash:
        return crypto.hash(pwd)
    ```

    **Effect Inference:**
    The compiler analyzes function bodies to determine effects:
        - Contains `~=` operator → Async
    - Calls async function → Async
    - No suspension or async calls → Sync (inferred)
    - Marked `sync fn` → Sync (enforced)

    **Benefits:**
    - **No function coloring:** Refactoring sync to async doesn't break callers
    - **Zero overhead:** Sync-inferred functions compile to plain functions
    - **Safety:** Effect system prevents blocking in async contexts
    - **Simplicity:** Most functions "just work" without annotations

    **Implementation:** When implemented, this will require:
        - Parser support for `sync fn` keyword
    - Effect inference algorithm in compiler
    - Promise type for async returns
    - Runtime support for suspension/resumption

## Function Declaration Semantics

        A standard `fn` declaration creates an async-capable function. The function
        body can use the suspension operator (`~=`) to yield control to the async
        runtime while waiting for operations to complete.

        **Type Signature Transformation:**
        ```
        Declared:  fn fetch() -> User
        Actual:    fn fetch() -> Promise<User>
        ```

        The return type is automatically wrapped in `Promise<T>` for async functions.
        Callers use the suspension operator to unwrap the promise:
            ```simple
        val user ~= fetch()  # Suspends until promise resolves
        ```

        **Contrast with Sync Functions:**
        - `fn` = async-capable, can suspend
        - `sync fn` = synchronous, cannot suspend

        **Implementation Note:** Parser currently doesn't support `async` semantics
        or suspension operators. These tests will be enabled when the feature is ready.

## Explicit Synchronous Functions

        The `sync fn` keyword declares a function that is guaranteed to never suspend.
        This is useful for:
            - Performance-critical code paths
        - Functions that must complete without yielding
        - Low-latency operations
        - CPU-bound computations

        **Syntax:**
        ```simple
        sync fn compute(x: i64) -> i64:
            return x * x
        ```

        **Compiler Guarantees:**
        - Function cannot use suspension operator (`~=`)
        - Function cannot call async functions
        - Return type is `T` (not `Promise<T>`)
        - Compiled with zero async overhead

        **Effect Checking:**
        The compiler validates sync constraints:
            ```simple
        sync fn bad():
            val x ~= fetch()  # ERROR: suspension in sync function
        ```

        **Use Cases:**
        - Hot loops in game engines
        - Cryptographic operations
        - Signal handlers
        - Real-time systems

        **Implementation Note:** Parser doesn't yet recognize `sync fn` keyword.
        These tests will be enabled when syntax support is added.

## Automatic Promise Type Wrapping

    Async functions automatically wrap their return type in `Promise<T>`. This
    transformation is transparent to the programmer - you write `-> User` but
    the function actually returns `Promise<User>`.

    **Type Transformation:**
    ```
    User-written:    fn fetch() -> User
    Compiler sees:   fn fetch() -> Promise<User>
    ```

    **Unwrapping with Suspension Operator:**
    ```simple
    fn get_user(id: UserId) -> User:
        val user ~= fetch(id)  # ~= unwraps Promise<User> to User
        return user
    ```

    **Contrast with Sync Functions:**
    ```simple
    sync fn double(x: i64) -> i64:
        return x * 2
    # Return type: i64 (NOT Promise<i64>)
    ```

    **Promise Characteristics:**
    - Represents a value that will be available in the future
    - Can be in three states: Pending, Fulfilled, Rejected
    - Suspension operator blocks current async context until resolved
    - Cannot be unwrapped in sync contexts

    **Implementation Note:** Promise type not yet implemented. These tests will
    be enabled when Feature #41 (Concurrency Primitives) is complete.

## Return Type Transformation Rules

        The compiler applies different type transformations based on function effect:

        **Async Function:**
        ```simple
        fn fetch_user(id: UserId) -> User:  // User writes this
            val resp ~= http.get("/users/{id}")
            return parse(resp)
        // Actual signature: fn fetch_user(id: UserId) -> Promise<User>
        ```

        **Sync Function (Inferred):**
        ```simple
        fn double(x: i64) -> i64:  // User writes this
            return x * 2
        // Actual signature: fn double(x: i64) -> i64 (no change)
        ```

        **Sync Function (Explicit):**
        ```simple
        sync fn compute(x: i64) -> i64:  // User writes this
            return x * x
        // Actual signature: fn compute(x: i64) -> i64 (enforced)
        ```

        **Effect-Based Transformation:**
        ```
        if effect = Async:
            T → Promise<T>
        else if effect = Sync:
            T → T
        ```

        **Multiple Returns:**
        All return statements must produce values of the base type `T`.
        The Promise wrapping is applied automatically by the compiler.

        ```simple
        fn conditional_fetch(use_cache: bool) -> Data:
            if use_cache:
                return cached_data  // Returns Data
            else:
                val data ~= fetch()  // Suspends, gets Data
                return data         // Returns Data
        // Both paths return Data, function returns Promise<Data>
        ```

## Effect Type Propagation

    Simple's effect system tracks whether functions are sync or async and enforces
    effect propagation rules to prevent common concurrency bugs.

    **Effect Lattice:**
    ```
    Async    (can call anything)
      ↓
    Sync     (can only call sync)
    ```

    **Propagation Rules:**

    1. **Sync calling Async → Error**
       ```simple
       sync fn process():
           val data = fetch()  // ERROR: sync cannot call async
       ```

    2. **Async calling Sync → OK**
       ```simple
       fn process():
           val result = compute(42)  // OK: async can call sync
       ```

    3. **Async calling Async → OK**
       ```simple
       fn process():
           val data ~= fetch()  // OK: async can call async
       ```

    4. **Sync calling Sync → OK**
       ```simple
       sync fn process():
           val result = compute(42)  // OK: sync can call sync
       ```

    **Why This Matters:**

    Preventing sync→async calls ensures:
        - Sync functions never accidentally block on async operations
    - Performance guarantees for sync-marked code
    - Clear boundaries between sync and async code

    **Error Messages:**
    When a sync function tries to call async code, the compiler produces
    a helpful error with suggestions:
        ```
    error: sync function cannot call async function
       |
     5 |     val x = fetch()
       |             ^^^^^^^ async function
       |
    help: remove 'sync' keyword or use suspension operator
    ```

    **Implementation Note:** Effect checking not yet implemented. These tests
    will be enabled when Feature #46 (Effect Inference) is complete.

## Sync → Async Call Restriction

        A synchronous function marked with `sync fn` cannot call asynchronous functions.
        This is a compile-time error enforced by the effect system.

        **Rationale:**

        If sync functions could call async functions, they would need to:
            - Either block the thread (defeating async purpose)
        - Or suspend (violating sync guarantee)

        Neither is acceptable, so the compiler forbids it.

        **Example Error:**
        ```simple
        sync fn bad_example():
            val data = fetch_from_api()  // ERROR!
            return process(data)
        ```

        **Compiler Error:**
        ```
        error[E0001]: sync function cannot call async function
          --> example.spl:2:16
           |
         1 | sync fn bad_example():
           | ---------------------- this function is sync
         2 |     val data = fetch_from_api()
           |                ^^^^^^^^^^^^^^^ this function is async
           |
           = note: sync functions can only call sync functions
           = help: remove 'sync' keyword to allow async calls
        ```

        **Solutions:**

        1. **Remove `sync` keyword:**
           ```simple
           fn good_example():  # Now async-capable
               val data ~= fetch_from_api()
               return process(data)
           ```

        2. **Use only sync operations:**
           ```simple
           sync fn good_example():
               val data = read_from_cache()  # Sync operation
               return process(data)
           ```

        **Implementation:** Requires effect inference and checking (Feature #46)
