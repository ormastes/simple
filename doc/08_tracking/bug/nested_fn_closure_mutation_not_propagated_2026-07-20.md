# Bug: nested `fn` passed by value as a callback does not propagate mutation of an outer `var` back to the caller

- **Date:** 2026-07-20
- **Status:** resolved 2026-11-25 — the silent non-propagation no longer reproduces; captured-variable assignment in a nested `fn` is now a loud compile error (owner ruling 2026-09-27, see verification note below)
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

## Verification 2026-11-25 (release/1.0.0 @ 4c6024f8271, Windows host) — resolved

Ran the exact minimal repro from this bug with the pinned seed
(`SIMPLE_LIB=src bin/simple.exe run repro.spl`). The silent wrong answer
(`executed = false` after the assignment ran) no longer occurs. Instead the
module fails loudly before execution:

```
error: compile failed: semantic: ... cannot assign to captured variable
`executed` inside nested fn `set_executed` (line 11): closures capture
enclosing locals by value and are read-only; return the new value or use a
module-level `var`
```

This matches the owner ruling now recorded in `.claude/rules/language.md:30`:
a nested `fn`/lambda assigning an enclosing local is a compile error in both
the seed and the pure-Simple interpreter; the capture-by-value limitation is
deliberate language semantics with an actionable diagnostic, not a silent
miscompile. `test/shared/control_flow/fn_lambda_spec.spl` was updated to the
same semantics (its "works with context/it blocks" example now observes block
execution through the block's RETURN value and cites lint CLOS001).

The defect as filed — a mutation that executes but silently does not propagate
— is therefore fixed (loud rejection replaces wrong output). The spec itself
could not be re-run end-to-end on this host: `bin/simple.exe test` fails
repo-wide at HEAD with `unknown decorator '@representation_boundary'`
(seed/source skew); the spec source was verified by inspection instead.
