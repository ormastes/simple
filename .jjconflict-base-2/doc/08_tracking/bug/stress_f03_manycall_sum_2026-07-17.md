# Cert stress f03: 300-call-chain sum — compiled/JIT path fixed already; interpreter-only divergence remains (separate, narrower root cause found)

- **Date documented:** 2026-07-17 (cert stress-suite salvage)
- **Date re-verified:** 2026-07-17 (STRESS lane)
- **Status:** PARTIALLY RESOLVED.
  - Default execution path (`simple run`, resolves to Cranelift JIT) — the
    path the stress-suite's own `_run` helper actually exercises — NO LONGER
    REPRODUCES. Fixed by some earlier, unrelated commit already on `main`
    before this lane started (not bisected — out of scope; evidence below).
  - Interpreter fallback (`SIMPLE_EXECUTION_MODE=interpret`) STILL gives a
    wrong result, but the root cause turned out to be a much narrower,
    different bug than the original "call-chain miscompute" hypothesis — see
    below. Left OPEN (not fixed by this lane): the fix is a deliberate
    dispatch-priority policy change with cross-cutting risk, out of scope for
    a stress-suite re-verification lane. See "Residual interpreter-only
    finding" below.
- **Area:** Interpreter call dispatch,
  `src/compiler_rust/compiler/src/interpreter_call/mod.rs` /
  `src/compiler_rust/compiler/src/interpreter_call/builtins.rs`.
- **Source:** `test/cert/stress/findings/f03_manycall_sum_wrong.spl` (defines
  `f0()`..`f299()`, each returning its index; `main` prints
  `f0()+f1()+...+f299()`, correct sum `44850`).

## Original symptom (as documented 2026-07-17, cert stress-suite salvage)

- compiled backend printed `64695813934153728` (garbage)
- interpreter printed `44786` (wrong, but plausible-looking)
- Both wrong; summing 300 integer *literals* directly was correct in both
  modes, so the original hypothesis was a fault specific to evaluating a long
  chain of *function-call* operands (stack-slot reuse / arg-passing
  suspected).

## Re-verification (2026-07-17)

```
$ SIMPLE_EXECUTION_MODE=cranelift src/compiler_rust/target/release/simple run f03_manycall_sum_wrong.spl
44850          # CORRECT (was 64695813934153728)
$ SIMPLE_EXECUTION_MODE=interpret src/compiler_rust/target/release/simple run f03_manycall_sum_wrong.spl
44786          # STILL WRONG, same wrong value as originally documented
$ src/compiler_rust/target/release/simple run f03_manycall_sum_wrong.spl   # default (no override)
44850          # CORRECT — this IS what the gate's `_run` helper invokes
```

The compiled/JIT-backend "garbage huge number" defect is gone; the gate's
own default invocation (what `scripts/check/cert/stress-suite.shs` actually
runs) now produces the correct answer. This is the behavior that matters for
the CORE gate, so f03 no longer reproduces there and has been promoted from
`findings/` into a pinned CORE `valid_case`.

## Residual interpreter-only finding (isolated, NOT the original "call chain" hypothesis)

The interpreter's wrong `44786` is not a call-chain-depth artifact at all.
Isolated repro:

```
fn f64() -> int:
    return 64
fn main():
    print(f64())
```

- Cranelift/JIT: prints `64` (correct — resolves the user's function).
- Interpreter: prints `0` (WRONG — silently ignores the user function).

`44850 - 44786 == 64` exactly: the ONLY miscounted term in the 300-call chain
is `f64()`, because `f64` is also the name of a builtin numeric-cast
function (`f64(x)` / `float(x)`, converts to float). In
`interpreter_call/mod.rs::evaluate_call`, builtins are checked **before**
user-defined functions by explicit design:

```rust
// Priority 2: Try built-ins (before user functions, so builtins can't be shadowed)
if let Some(result) = builtins::eval_builtin(name, args, ...)? {
    return Ok(result);
}
...
// Priority 5: Check regular functions (user-defined) — most common case
if let Some(func) = functions.get(name).cloned() { ... }
```

`builtins.rs`'s `"f64" | "float"` arm calls
`eval_arg(args, 0, Value::Float(0.0), ...)` — when `args` is empty (as in a
zero-arg call `f64()`), it silently defaults to `0.0` rather than erroring or
falling through, so `f64()` returns `Value::Float(0.0)` -> coerced to `0`
under the `-> int` context, discarding the user's `fn f64() -> int: return
64` entirely.

This is a genuine interpreter/compiled-backend **semantic divergence**: the
Cranelift/LLVM MIR-lowering path does NOT reserve primitive-type names
(`f64`, `i32`, `u8`, ...) against user redefinition — it resolves `f64()` to
the user's function correctly — but the interpreter's dispatch order
explicitly and intentionally reserves them ("so builtins can't be
shadowed", per the comment at the Priority-2 check).

### Why this lane did NOT fix the residual finding

1. It is an explicit, commented design decision in the interpreter
   (`evaluate_call`'s builtin-before-user-function ordering), not an
   accidental oversight — reversing or special-casing it needs owner
   sign-off, not a unilateral change from a stress-verification lane.
2. It does not affect the CORE gate's own invocation (`simple run` with no
   mode override resolves to the JIT path, which is already correct).
3. A minimal, scoped fix (e.g., only fall through to the user function when
   the builtin arm would otherwise use a default/absent argument) still
   changes cross-cutting interpreter call semantics and needs test coverage
   beyond this lane's remit ("never over-engineer").

### Recommended follow-up (not applied here)

Either (a) make `eval_builtin`'s cast arms for `i8`/`i16`/.../`f64`/`bool`
require their argument (error instead of defaulting to 0/0.0 when `args` is
empty) so a zero-arg call falls through to Priority 5's user-function lookup,
or (b) check `functions.contains_key(name)` before the builtins priority
check specifically for the primitive-type-cast names, mirroring the existing
extern-vs-local-def precedence already used one priority level up (see the
`has_local_def` comment just above Priority 2 in the same function, which
solves the identical shadowing problem for extern functions). Either fix is
narrow but touches shared interpreter dispatch — needs its own verification
pass across the interpreter test suite, not bundled into this stress-gate
re-verification.

## Verification

```
cd src/compiler_rust && cargo build --release
SIMPLE_BIN=src/compiler_rust/target/release/simple sh scripts/check/cert/stress-suite.shs
```
