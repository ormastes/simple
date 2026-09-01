# Bug: `GenericClass<T>.static_method()` unresolved under `simple test` (non-generic classes work fine)

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/futures_promises_spec.spl`)
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
