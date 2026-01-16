# promise_type_spec

*Source: `simple/std_lib/test/features/concurrency/promise_type_spec.spl`*

---

Promise Type - Feature #47

Overview:
    Promise<T> represents async computation result. Supports then/catch/finally
    chaining, all/race/any combinators, and implicit wrapping for async functions.
    Integrates with effect inference system.

Syntax:
    val p = Promise.resolve(42)                 # Create resolved promise
    val p = Promise.reject(Error("failed"))     # Create rejected promise
    fetch_user(id).then(\u: u.name)             # Chain with then
    fetch_user(id).catch(\e: default_user())    # Handle errors
    Promise.all([f1, f2, f3])                   # Wait for all

Implementation:
    - Promise<T> type for async computations
    - Static constructors: resolve, reject
    - Chaining: then, catch, finally
    - Combinators: all, race, any, all_settled
    - State inspection: is_pending, is_fulfilled, is_rejected
    - Implicit wrapping for async function returns
    - Avoids double wrapping

Notes:
    - Promise type integrates with effect inference
    - Async functions return Promise<T> implicitly
    - Supports method chaining for error handling
    - Planned feature - not yet implemented
