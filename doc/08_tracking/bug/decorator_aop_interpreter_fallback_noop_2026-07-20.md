# Bug (interpreter-path, unverified against compiled): `@decorator` wrapping and AOP `pc{}` weaving are no-ops under the tree-walking interpreter fallback

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/{decorators,aop,aop_pointcut}_spec.spl`, `collections_spec.spl` "Decorators" section)
- **Area:** interpreter fallback path (`bin/simple test` / `bin/simple run` on the
  deployed seed `bin/release/x86_64-unknown-linux-gnu/simple`, which falls back to
  tree-walking whenever JIT lowering fails — the default/only path available on
  this host per `doc/08_tracking/bug/host_toolchain_seed_pinned_lint_fmt_doccov_unrunnable_2026-07-17.md`)

## Symptom

`decorators_spec.spl` ("Status: Implemented"), 4 failures — every `@decorator`
wraps a locally-defined function but the wrapper is never invoked; the target
runs completely undecorated:

```
✗ applies basic decorator          : expected 6 to equal 12   (6 = 5+1 undecorated; 12 = (5+1)*2)
✗ applies decorator with arguments : expected 11 to equal 33  (11 = 10+1 undecorated; 33 = (10+1)*3)
✗ stacks multiple decorators       : expected 5 to equal 20   (5 = identity undecorated)
✗ uses decorator without parens    : expected 16 to equal 21  (16 = 4*4 undecorated; 21 = 16+5)
```

`collections_spec.spl`'s "Decorators" describe block shows the identical
pattern (2 failures, same numbers as decorators_spec's first two examples).

`aop_spec.spl` ("Status: In Progress") and `aop_pointcut_spec.spl` ("Status: In
Progress") show the same class of failure for `on pc{...} use advice
before/after priority N` declarations: the advice function is never invoked,
so `var matched = false` / `var count = 0` guard variables never flip
(`expected false to equal true`, `expected 0 to equal N`) across ~19 examples
combined. Both files' own docstrings already flag this as a known limitation:
"Inline module definitions in test blocks not supported" and (for AOP)
"Compile-time weaving for before/after, runtime for around".

## Root cause (module-level repro, not just nested-in-`it`)

Minimal repro at **module scope** (not inside a `describe`/`it` block, ruling
out the "inline in test blocks" theory as the sole cause):

```simple
fn double_result(f):
    fn wrapper(x):
        return f(x) * 2
    return wrapper

@double_result
fn add_one(x):
    return x + 1

fn main():
    print("add_one(5) = " + add_one(5).to_text())

main()
```

`bin/release/x86_64-unknown-linux-gnu/simple run <repro>.spl`:
```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Parameter 'f' in function 'double_result' requires explicit type annotation
add_one(5) = 6
```
Expected `12` (decorated). The JIT lowering fails first (unrelated: untyped
closure param), forcing fallback to the tree-walking interpreter, and under
that interpreter `@decorator` application is a pure no-op — `add_one` runs as
if undecorated even though `double_result` and the `@double_result` attribute
are both present and well-formed at module scope.

This is consistent with decorator wrapping being implemented as a compile-time
AST transform (attribute expansion) that the tree-walking interpreter fallback
never runs — the same story AOP's own docstring already tells for its
`pc{}` weaving ("Compile-time weaving for before/after"). Not confirmed against
`interpreter_extern`/HIR-lowering source in this pass.

## Fix direction (not applied)

Either (a) make the tree-walking interpreter also perform decorator-attribute
expansion / AOP pc{} weaving at eval time (a real feature gap), or (b) if
decorators/AOP are deliberately compile-time-only, make the interpreter fail
loudly on `@decorator`/`on pc{...}` rather than silently running the
undecorated body — the current silent no-op is a correctness hazard
independent of whether it's "by design" for this execution mode.

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/decorators_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/aop_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/aop_pointcut_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple run <module-level repro above>
```
**Not verified against the compiled/JIT/native path or the pure-Simple
self-hosted compiler** — no runnable self-hosted binary was available on this
host (redeploy walled, see the seed-pinned doc above). If decorators/AOP
weaving genuinely only run under compiled mode, this bug's practical severity
is "expected interpreter limitation, needs an explicit diagnostic" rather than
"feature broken everywhere" — flagging for whoever verifies against a real
compiled build.
