# Async/Await Interpreter Crashes - 2026-06-11

Status: partially-fixed (2026-06-11) — B1/B2(await) VERIFIED FIXED; B3(generator/actor scope) + B5(Promise/FutureValue) + B6(HIR I64) remain OPEN (Rust-seed only); B4(spawn SIGABRT) VERIFIED FIXED via E6; coverage gap documented.

**Fixed 2026-06-11 (commit 861e29bc99):** the SIGSEGV had already become silent
corruption (`await f()` always yielded 3 = NIL bit pattern in JIT mode; a
semantic error in interpreter mode). Root causes fixed:
- `rt_future_await` (runtime/src/value/async_gen.rs): non-Future input now
  returns the value itself (eager-async identity), not NIL.
- Interpreter `Expr::Await` (compiler/src/interpreter/expr.rs): non-Future/
  non-Actor values route through `await_value` (Promise extract + passthrough)
  instead of erroring.
`await f()` now returns the body value in BOTH default-JIT and forced
interpreter modes. Regression spec:
`test/01_unit/compiler/interpreter/async_await_eager_value_spec.spl` (3/3 — VERIFIED passing 2026-06-11).

**spawn fn() SIGABRT (B4) FIXED 2026-06-11 (E6):** `green_spawn(fn)` now stores
the closure in a `fn() -> i64` class field (`GreenTask.thunk`) and defers to
`green_run_one`/`green_run_all`. See
`doc/08_tracking/bug/green_thread_direct_runtime_blockers_2026-06-06.md` (E6).
Spec: `test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl`
(5/5 passing).

**Still open (all Rust-seed-rooted — do NOT fix in .spl):**
- B3: yield/generator + actor desugar HIR scope visibility (see below).
- B5: Promise-vs-FutureValue deep representation reconcile.
- B6: HIR hardcodes I64 for await result type (masked by eager semantics).

## Per-Item Triage Table (2026-06-11 audit)

| # | Item | Category | Status | Action |
|---|------|----------|--------|--------|
| B1 | SIGSEGV `await f()` → NIL (exit 139) | (a) Fixed | VERIFIED FIXED | commit 861e29bc99; spec 3/3 green |
| B2 | `await f()` yields 3/NIL in JIT/interpreter | (a) Fixed | VERIFIED FIXED | same commit; eager-async identity |
| B3 | `yield` / generator class not visible in HIR scope | (c) Rust-seed | OPEN | root-cause note below |
| B3b | `actor` desugar class not visible in HIR scope | (c) Rust-seed | OPEN | root-cause note below |
| B4 | `spawn fn()` closure SIGABRTs (exit 132) at cleanup | (a) Fixed | VERIFIED FIXED | E6 in green_thread_direct_runtime_blockers_2026-06-06.md |
| B5 | Promise vs FutureValue unreconciled in MIR executor | (c) Rust-seed | OPEN | root-cause note below |
| B6 | HIR hardcodes `TypeId::I64` for await result type | (c) Rust-seed | OPEN | root-cause note below |
| C1 | Coverage gap: 7 specs are single-skip placeholders | (b)/(c) mixed | DOCUMENTED | see Coverage section below |
| C2 | `async_integration_spec` has 21 hollow `expect(1).to_equal(1)` tests | (b) | DOCUMENTED | vacuous; needs real assertions when B3/B5 resolved |

## Summary

End-to-end `async fn` + `await` crashes the Rust-seed interpreter instead of
producing a value or a typed error. Found during the 2026-06-11 async audit
(plan: `doc/03_plan/language/concurrency/async_green_process_hardening.md`).

## Symptoms (probe programs, interpreter mode)

- `async fn f() -> i64: 42` + `val x = await f()` → SIGSEGV (exit 139). **FIXED.**
- `yield` in a generator fn → "yield called outside of generator" +
  "Unknown variable: gen" (desugared class not visible to HIR scope). **OPEN (B3).**
- `actor` definition → same desugar/HIR scope visibility failure. **OPEN (B3b).**
- `spawn fn()` runs, but the spawned closure SIGABRTs (exit 132) at cleanup. **FIXED (B4/E6).**

## Root Cause (diagnosed)

### B3 — Generator/Actor HIR Scope Visibility (Rust-seed)

The pure-Simple desugar pass (`src/compiler/10.frontend/desugar/desugar_async.spl`,
`desugar_module()`) correctly injects generated enums into `module.enums` and
generated poll functions into `module.functions`, and converts actors to
`module.classes`, before returning the desugared `Module`. The failure is in the
Rust HIR lowering layer: `src/compiler_rust/compiler/src/hir/lower/` builds the
HIR scope **before** the desugared module symbols are resolved, so generated
names (state enum type, poll function name, actor class name) are absent from
the scope when function bodies are lowered.

Minimal repro:
```
# generator fn
fn gen_counter():
    yield 1
    yield 2
# → interpreter: "yield called outside of generator" + "Unknown variable: gen"

actor Counter:
    val count: i64
# → interpreter: symbol lookup fails for Counter as a class
```

Fix required: in Rust, re-run scope population after desugar (or run desugar
before scope construction). File: `src/compiler_rust/compiler/src/hir/lower/mod.rs`
or the pipeline entry that sequences desugar vs HIR lowering. Authorized Rust
change only.

### B5 — Promise vs FutureValue Representation (Rust-seed)

The MIR executor calls `rt_future_await` on a Simple-level `Promise` object
(created by `wrap_in_promise` in the interpreter) while the Rust runtime's
`rt_future_await` (`src/compiler_rust/runtime/src/value/async_gen.rs`) expects a
`FutureValue` (a Rust-native type). The B1/B2 fix made `rt_future_await`
identity-safe for non-FutureValue input, but the underlying representation split
remains: Promise.poll() vs FutureValue.poll() are separate code paths.

Fix required: unify the two representations or add a conversion shim so that
`wrap_in_promise` produces a `FutureValue`-compatible value. Authorized Rust
change only. File: `src/compiler_rust/compiler/src/value_async.rs` +
`src/compiler_rust/runtime/src/value/async_gen.rs`.

### B6 — HIR Hardcodes I64 for Await Result Type (Rust-seed)

`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` lines ~193-200:
```rust
Expr::Await(inner) => {
    let future_hir = Box::new(self.lower_expr(inner, ctx)?);
    Ok(HirExpr {
        kind: HirExprKind::Await(future_hir),
        ty: TypeId::I64,   // ← hardcoded, ignores Future<T> inner type
    })
}
```
This is currently masked by eager-async semantics (the value is passed through
before type checking asserts on it), but will produce incorrect type information
once futures become lazy. Fix: extract the inner type `T` from `Future<T>` and
use it as the HIR expression type. Authorized Rust change only.

## Required Fix (prioritized)

1. **(DONE)** Guard `rt_future_await` against non-`FutureValue` input → typed error
   (removes the SIGSEGV class).
2. **(DONE)** Interpreter `Expr::Await` passthrough for non-Future values.
3. **(OPEN — Rust)** Re-inject desugared declarations into HIR scope before lowering bodies (B3).
4. **(OPEN — Rust)** Reconcile Promise vs FutureValue in the interpreter dispatch path (B5).
5. **(OPEN — Rust)** Propagate the real `Future<T>` inner type for `await` (B6).

## Coverage Gap

`test/01_unit/compiler/async/*` spec status (2026-06-11 audit):

| Spec | Tests | Status |
|------|-------|--------|
| async_spawn_analysis_spec.spl | 26 | GREEN (active, real tests) |
| async_reservation_analysis_spec.spl | 23 | GREEN (active, real tests) |
| async_await_eager_value_spec.spl | 3 | GREEN (B1/B2 regression) |
| async_integration_spec.spl | 21 | FALSE-GREEN (hollow — all `expect(1).to_equal(1)`) |
| async_desugar_integration_spec.spl | 1 | SKIP placeholder |
| async_frame_analysis_spec.spl | 1 | SKIP placeholder |
| async_state_machine_spec.spl | 1 | SKIP placeholder |
| async_pipeline_spec.spl | 1 | SKIP placeholder |
| async_mir_spec.spl | 1 | SKIP placeholder (comment: OOM via numbered dir resolution) |
| state_enum_spec.spl | 1 | SKIP placeholder (real tests commented out, lines 47–209) |
| suspension_analysis_spec.spl | 1 | SKIP placeholder (real tests commented out) |
| poll_generator_spec.spl | 1 | SKIP placeholder (real tests commented out) |

The commented-out tests in `state_enum_spec.spl`, `suspension_analysis_spec.spl`,
and `poll_generator_spec.spl` depend on `ExprKind` enum constructors which fail
in interpreter mode (see NOTE in `async_spawn_analysis_spec.spl` header). The
imports (`compiler.desugar.*`) resolve correctly — the `async_spawn_analysis_spec`
and `async_reservation_analysis_spec` use the same import path and are green.
The blocker for uncommenting those tests is `ExprKind` constructor availability
in interpreter mode, which is a Rust-seed limitation.

The `async_integration_spec.spl` hollow tests can be filled in pure Simple once
B3 (generator/actor HIR scope) is resolved in the Rust seed, since they exercise
`actor` and `async fn` end-to-end.
