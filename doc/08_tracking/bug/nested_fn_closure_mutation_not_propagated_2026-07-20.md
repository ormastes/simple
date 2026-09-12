# Bug: nested `fn` passed by value as a callback does not propagate mutation of an outer `var` back to the caller

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/shared/control_flow/fn_lambda_spec.spl`)
- **Area:** `src/compiler_rust` interpreter (tree-walking fallback, `bin/simple run` / `bin/simple test`, deployed seed at `bin/release/x86_64-unknown-linux-gnu/simple`)

## Symptom

`test/shared/control_flow/fn_lambda_spec.spl`, example `"works with context/it
blocks"` (line 95), fails:

```
✗ works with context/it blocks
  expected false to equal true
```

A nested named `fn` (`set_executed`) that assigns to an outer `var`
(`executed`), when passed **by value** to another nested function and invoked
there via `block()`, DOES run its body and DOES execute the assignment
statement (confirmed with `print` tracing), but the mutation is not visible in
the caller's scope after the call returns.

This matches the known runtime limitation already recorded in
`.claude/rules/language.md`: "Nested closure capture - can READ outer vars,
CANNOT MODIFY (module closures work fine)" -- this bug is a concrete,
reproducible instance of that limitation, filed as a standing tracked bug
since the language rule references it as a limitation rather than a fix.

## Minimal repro

```simple
fn main():
    var executed = false

    fn mock_context(name: text, block):
        print("in mock_context, calling block")
        block()
        print("after block call")

    fn set_executed():
        print("in set_executed, before assign")
        executed = true
        print("in set_executed, after assign")

    mock_context("test", set_executed)

    print("executed = " + executed.to_text())
```

Actual output (`bin/release/x86_64-unknown-linux-gnu/simple run <repro.spl>`):
```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown variable: mock_context while lowering main
in mock_context, calling block
in set_executed, before assign
in set_executed, after assign
after block call
executed = false
```

Expected: `executed = true` (the assignment inside `set_executed` should
mutate the same outer `var` that `main`'s `print` reads afterward, since
`set_executed` is a closure defined in the same lexical scope as `executed`).

Note there is also a secondary symptom worth flagging separately if not
already tracked: the JIT reports `HIR lowering error: Unknown variable:
mock_context while lowering main` and silently falls back to the tree-walking
interpreter -- `mock_context` is itself a nested `fn` referenced by name as a
plain value (`mock_context("test", set_executed)` calls it directly, but the
error suggests the JIT's HIR lowering doesn't resolve nested-fn identifiers
the same way the interpreter does). This repro focuses on the interpreter
fallback's closure-mutation result since that is what the failing spec
exercises end-to-end.

## Root cause (hypothesis, not confirmed against source)

Likely the closure environment captured for a nested `fn` value (when that
`fn` is referenced as a first-class value, e.g. passed as an argument, rather
than called directly by name in its own enclosing scope) is captured
by-value/snapshot instead of by-reference to the parent scope's variable
slot, so an assignment inside the closure body writes to a local copy of
`executed` in the captured environment rather than back into `main`'s scope.
This is consistent with `.claude/rules/language.md`'s existing note that
"module closures work fine" (i.e., top-level/module-scope capture uses a
shared reference) while nested-block closures do not. Not verified against
`src/compiler_rust/compiler/src/interpreter/` source in this pass; the
interpreter's closure-value construction and its `Env`/scope-chain handling
for nested `fn` are the suspect area (see `Value::Function { captured_env,
.. }` construction sites in `src/compiler_rust/compiler/src/interpreter*/`).

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/shared/control_flow/fn_lambda_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple run <repro.spl above>
```
Both the full spec (`fn_lambda_spec.spl`, example "works with context/it
blocks") and the trimmed standalone repro above reproduce the same
false-instead-of-true result. Not checked against the pure-Simple self-hosted
compiler/interpreter (`src/compiler/`) -- only the Rust seed was probed, and
per repo convention that seed's interpreter fallback is the default path
`bin/simple test`/`bin/simple run` exercise when JIT lowering fails.

## Triage 2026-09-12 — still reproduces; minimal repro with both controls

Binary: `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` sha256 `3d120a6f`

```simple
class Cell:
    var n: i64

fn bump(c: Cell):
    c.n = c.n + 1

fn main():
    val c = Cell { n: 0 }
    c.n = 5
    print("direct=", c.n)
    bump(c)
    print("via-free-fn=", c.n)
    fn nested():
        c.n = 99
    nested()
    print("via-nested-fn=", c.n)
```

```
$ SIMPLE_RUST_SEED_WARNING=0 bin/simple run g_ctrl.spl
direct= 5
via-free-fn= 6
via-nested-fn= 6     <-- the nested fn's write of 99 is LOST
```

The two controls are what make this decisive. Direct assignment works, and mutation
through a FREE function that takes the same class handle as a parameter works
(0 -> 5 -> 6), so class reference semantics are intact. Only the write performed
inside a nested `fn` that CAPTURES the enclosing local is dropped — and `Cell` is a
class, i.e. a reference type, so this is not the "arrays are value types" copy
semantics. The captured binding is being written in a scope that is discarded.

Blast radius measured in the same pass: this is what blocks
`promise_new_push_reassign_same_scope_as_nested_closure_2026-07-29`.
`test/01_unit/lib/std/concurrency/promise_spec.spl` is currently
`declared>=19 executed=19 passed=12 failed=7`, every failure
`semantic: unknown static method new on class Promise`, and a `static fn new`
cannot be written correctly in pure Simple while this defect stands — a
class-instance cell captured by the executor's `resolve`/`reject` closures loses
the write exactly as above (probe returned `resolved= false`). So the record's
"module-level array push+reassign" framing is narrower than the defect: the cell
being an array is irrelevant.

Not fixable from pure Simple: `bin/simple` is the Rust bootstrap seed, so this is
`src/compiler_rust/compiler/src/interpreter/expr/control.rs`.

- Status: OPEN (2026-09-12) — reproduced on 3d120a6f, minimal repro above, needs a Rust-seed change
