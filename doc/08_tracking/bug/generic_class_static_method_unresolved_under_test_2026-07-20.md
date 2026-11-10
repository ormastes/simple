# Bug: `GenericClass<T>.static_method()` unresolved under `simple test` (non-generic classes work fine)

- **Date:** 2026-07-20
- **Status:** CLOSED 2026-11-11 — FIXED on release; verified by lane ne10 (seed 46fe8f6b6def)
- **Area:** interpreter method-call dispatch for generic classes (likely
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs`, same family as
  `doc/08_tracking/bug/enum_impl_static_fn_method_call_path_skips_impl_methods_2026-07-20.md`),
  deployed seed at `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

`futures_promises_spec.spl` ("Status: In Progress") defines a self-contained
`class Promise<T>:` with `static fn new/resolved/rejected` declared **inline in
the class body** (not a separate `impl` block). 9 of ~15 examples fail, all at
the very first line of the `it` block:

```
✗ maps future to new value
  semantic: unknown static method resolved on class Promise
✗ chains multiple map operations
  semantic: unknown static method resolved on class Promise
... (7 more, identical error, different call sites all being `Promise.resolved(...)` / `Promise.new(...)`)
```

## Minimal repro

```simple
class Box<T>:
    value: T

    static fn wrap(v: T) -> Box<T>:
        Box(value: v)

describe "repro":
    it "calls generic static method":
        val b = Box.wrap(42)
        expect b.value == 42
```

`bin/release/x86_64-unknown-linux-gnu/simple test <repro>.spl --no-session-daemon`:
```
✗ calls generic static method
  semantic: unknown static method wrap on class Box
```

Control (non-generic class, otherwise identical):

```simple
class Box:
    value: i64

    static fn wrap(v: i64) -> Box:
        Box(value: v)

describe "repro":
    it "calls non-generic static method":
        val b = Box.wrap(42)
        expect b.value == 42
```
→ **passes** (`1 example, 0 failures`).

The only difference between the two repros is the class's generic parameter
(`class Box<T>:` vs `class Box:`). The static method is declared identically
(inline in the class body) in both. This isolates the defect to generic
classes specifically, not to "inline vs `impl` block" (which is the mechanism
in the enum sibling bug above) or to nested test-block scope (both repros are
inside a `describe`/`it` block equally).

## Root cause

Not confirmed against source in this pass (out of scope: would need a Rust
rebuild to iterate). Given the sibling enum bug's confirmed root cause (two
separate dispatch code paths for `TypeName.method(...)`, only one of which
consults the full method table, with the SSpec `it`-block call path using the
narrower one), the likely mechanism is the same dispatch-path split, with the
narrower path additionally failing to resolve static methods when the
receiver's type carries generic parameters (e.g. it looks up `Box<T>` instead
of the base type name `Box` in whatever table it consults).

## Fix direction (not applied — compiler-internals change, needs rebuild)

Locate the `Value::ClassType`/`Value::GenericClassType`-shaped dispatch arm
used by the SSpec `it`-block call-expression path (see the enum sibling bug's
"Root cause" section for the two known call sites in
`interpreter_method/mod.rs` vs `interpreter/expr/calls.rs`) and confirm generic
class instances aren't being looked up under a mangled/parameterized type name
that the static-method table doesn't have an entry for.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/futures_promises_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <repro spec above> --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test <non-generic control spec above> --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or the JIT/native
path — only the Rust seed interpreter (the path `bin/simple test` exercises on
this host) was probed.

---

## 2026-11-11 addendum — lane ne10 (P3 traverse, batch ne10)

**Verdict: FIXED on release.**

- **Fixing commit:** `2a488e2cf130` `fix(hir): apply nominal generic declaration defaults and
  arity` (branch tip of PR #7597, merged as `9e7e7a526edb`, 2026-11-07; ancestor of release tip).
  This matches the root-cause hypothesis recorded above: generic class instances were being
  looked up under a parameterized/mangled type name the static-method table had no entry for;
  the HIR nominal-generic-owner work makes the declared owner resolve.
- **Verification (seed-smoke, tracked seed `bin/simple.exe` build-commit `46fe8f6b6def`,
  `--mode=interpreter --no-cache`):**
  - The doc's minimal repro (`class Box<T>` + inline `static fn wrap`, control included) now
    passes: `1 example, 0 failures` — the
    `semantic: unknown static method wrap on class Box` error no longer reproduces.
  - The original trigger `test/feature/usage/futures_promises_spec.spl` now executes all 15
    examples (`Results: 15 total, 14 passed, 1 failed`). Every
    `Promise.new/resolved/rejected(...)` static call resolves and runs; on 2026-07-20, 9 of ~15
    failed at the first line with `unknown static method resolved on class Promise`.
  - The one remaining failure (`retries failed future`:
    `expected Promise(state: PromiseState::Resolved(100), callbacks: []) to equal 100`) is a
    spec expectation mismatch (a Promise object compared to a bare `100`), not this dispatch
    defect.
