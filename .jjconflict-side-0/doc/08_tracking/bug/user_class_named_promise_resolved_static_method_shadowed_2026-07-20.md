# A user-defined `class Promise<T>` with a `static fn resolved(...)`/`rejected(...)` is shadowed by the builtin async `Promise` class name

**Date:** 2026-07-20
**Component:** Rust interpreter static-method dispatch for a locally-defined
class whose name (`Promise`) collides with the interpreter's builtin
async/await `Promise` support
(`src/compiler_rust/compiler/src/interpreter_call/core/async_support.rs`,
`src/compiler_rust/compiler/src/interpreter/async_support.rs`, both of which
special-case `class == "Promise"` for wrapping async-function return values).
**Severity:** Medium — narrow (only triggers when a user's own class is
literally named `Promise` and defines a static method the builtin doesn't
also happen to define), but a hard, universal failure once triggered
(confirmed under both `run` and `test` — not the `test`-vs-`run` evaluator
landmine).

## Symptom

`test/feature/usage/futures_promises_spec.spl` defines its own `enum
PromiseState` + `class Promise<T>` at module scope (not imported from any
stdlib package) with `static fn new(executor)`, `static fn
resolved(value: T)`, and `static fn rejected(error)`. 9 of 15 examples fail,
every one that (directly or via `.map()`/`.catch()`/etc. internally calling
`Promise.resolved`/`Promise.rejected`) reaches one of those two static
methods:

```
semantic: unknown static method resolved on class Promise
```

`Promise.new(...)` — defined identically as a `static fn` on the same class
— works fine (2 passing examples use it directly).

## Minimal repro — universal, not test-vs-run specific

```simple
enum PromiseState:
    Pending
    Resolved(value)

class Promise<T>:
    state: PromiseState

    static fn resolved(value: T) -> Promise<T>:
        Promise(state: PromiseState.Resolved(value))

fn main():
    val p = Promise.resolved(21)
    match p.state:
        case PromiseState.Resolved(v):
            print(v)
        case _:
            print(-1)

main()
```

`bin/release/x86_64-unknown-linux-gnu/simple run <this file>` →
```
error: semantic: unknown static method resolved on class Promise
```
(reproduces identically under `bin/simple test`.)

## Isolation (confirms it's the class NAME "Promise", not the method name or generics)

1. Renaming only the static method (`resolved` → `make_resolved`, same
   generic `class Promise<T>`, same body) → works, prints `21`.
2. Renaming only the class (`class Widget:` instead of `class Promise<T>:`,
   dropping the generic param, keeping the method named `resolved`) →
   works, prints `99` for `Widget.resolved(99)`.
3. Only the combination — a class literally named `Promise` with a static
   method named `resolved` (or `rejected`) — fails.

This points at the interpreter's builtin async-support code
(`async_support.rs` in both `interpreter/` and `interpreter_call/core/`),
which special-cases `class == "Promise"` (`wrap_in_promise`, used to box
async-function return values into `Value::Object { class: "Promise", ... }`)
— static-method dispatch for a class named `Promise` likely consults this
builtin machinery (or a registry entry it populates) instead of, or before,
the user's own `class Promise<T>` static-method table, and that path
apparently only recognizes whatever method set the builtin path itself uses
(`new` evidently overlaps by coincidence; `resolved`/`rejected` don't).

## Root-cause hypothesis (not confirmed further — out of scope for a spec-triage pass, needs a rebuild to verify any fix)

Static-method resolution for a class named `Promise` may route through (or
get intercepted by) the async/await builtin-Promise machinery in
`async_support.rs` rather than falling through cleanly to a user-defined
`class Promise<T>`'s own static-method table. Needs Rust-side tracing of the
static-method-call resolution path (wherever `"unknown static method %s on
class %s"` is raised) to see where/how it distinguishes builtin-Promise
from user-Promise.

## Notes

- Do NOT attempt a Rust seed source fix here (out of scope for a
  spec-triage pass; needs a rebuild to verify).
- This is a genuinely different symptom from the already-tracked
  `generic_class_static_method_unresolved_under_test_2026-07-20.md` landmine
  (imported-class static methods unresolved *only* under `test`): here the
  class is defined locally in the same file (not imported), and the failure
  is universal across both `run` and `test`, so it is filed as a distinct
  bug rather than appended to that doc.
- No spec assertions were weakened; all 9 examples are left correctly RED.

## Affected specs

- test/feature/usage/futures_promises_spec.spl (9 of 15 examples: `maps
  future to new value`, `chains multiple map operations`, `flattens nested
  futures`, `chains async operations with flatMap`, `recovers with fallback
  value`, `retries failed future`, `combines multiple futures`, `handles
  timeout on future`, `cancels pending future`)

Verified with:
`SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/futures_promises_spec.spl --no-session-daemon 2>&1 | sed 's/\x1b\[[0-9;]*m//g'`
→ `Passed: 6, Failed: 9`
