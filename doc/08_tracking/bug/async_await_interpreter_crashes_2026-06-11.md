# Async/Await Interpreter Crashes - 2026-06-11

Status: partially-fixed (2026-06-11) — B1/B2(await) VERIFIED FIXED; B3(generator runtime) OPEN; B3b(actor HIR scope) FIXED IN SEED — pending redeploy; B4(spawn SIGABRT) VERIFIED FIXED via E6; B5(Promise/FutureValue) OPEN; B6(HIR I64) FIXED IN SEED — pending redeploy; coverage gap documented.

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
- B3: generator/yield runtime interpreter crash (exit 132 SIGABRT) — HIR lowering is correct, crash is in interpreter execution of yield. Separate from B3b.
- B5: Promise-vs-FutureValue deep representation reconcile.
- ~~B3b: actor desugar class not visible in HIR scope~~ → **FIXED IN SEED (S6 batch, pending redeploy):** `Node::Actor` registered in Pass 0 + `register_declarations_from_node` via `register_class`. 5 regression tests green (`hir::lower::tests::async_desugar_tests`). Binary verified: `actor Counter: val count: i64` + no-ctor usage exits 0 cleanly.
- ~~B6: HIR hardcodes I64 for await result type~~ → **FIXED IN SEED (S5 batch, pending redeploy):** `ty: TypeId::I64` replaced with `ty: operand_ty` (the inner expression's type). Rust tests: `test_await_expr_type_propagates_operand_type` + `test_await_expr_string_type_propagates` both green.

## Per-Item Triage Table (2026-06-11 audit)

| # | Item | Category | Status | Action |
|---|------|----------|--------|--------|
| B1 | SIGSEGV `await f()` → NIL (exit 139) | (a) Fixed | VERIFIED FIXED | commit 861e29bc99; spec 3/3 green |
| B2 | `await f()` yields 3/NIL in JIT/interpreter | (a) Fixed | VERIFIED FIXED | same commit; eager-async identity |
| B3 | `yield` / generator runtime interpreter crash (SIGABRT) | (c) Rust-seed | OPEN | HIR lowering is correct; crash in interpreter executor |
| B3b | `actor` desugar class not visible in HIR scope | (c) Rust-seed | FIXED IN SEED — pending redeploy | S6: `Node::Actor` in Pass 0 + register_class; 5 tests green |
| B4 | `spawn fn()` closure SIGABRTs (exit 132) at cleanup | (a) Fixed | VERIFIED FIXED | E6 in green_thread_direct_runtime_blockers_2026-06-06.md |
| B5 | Promise vs FutureValue unreconciled in MIR executor | (c) Rust-seed | OPEN | root-cause note below |
| B6 | HIR hardcodes `TypeId::I64` for await result type | (c) Rust-seed | FIXED IN SEED — pending redeploy | S5 batch: `ty: operand_ty`; tests green |
| C1 | Coverage gap: 7 specs are single-skip placeholders | (b)/(c) mixed | DOCUMENTED | see Coverage section below |
| C2 | `async_integration_spec` has 21 hollow `expect(1).to_equal(1)` tests | (b) | DOCUMENTED | vacuous; needs real assertions when B3/B5 resolved |

## Summary

End-to-end `async fn` + `await` crashes the Rust-seed interpreter instead of
producing a value or a typed error. Found during the 2026-06-11 async audit
(plan: `doc/03_plan/language/concurrency/async_green_process_hardening.md`).

## Symptoms (probe programs, interpreter mode)

- `async fn f() -> i64: 42` + `val x = await f()` → SIGSEGV (exit 139). **FIXED.**
- `yield` in a generator fn → runtime SIGABRT (exit 132); HIR lowering itself succeeds. **OPEN (B3 — interpreter-level).**
- `actor` definition → HIR scope visibility failure (symbol lookup fails for actor as a class). **FIXED IN SEED (B3b, S6 batch, pending redeploy).** Before fix: "symbol lookup fails for Counter as a class". After fix (verified on fresh binary): `actor Counter: val count: i64` exits 0 with no error. Constructor instantiation (`Counter { count: 0 }`) hits a pre-existing field-type-inference limitation that also affects structs; that is a separate unrelated bug.
- `spawn fn()` runs, but the spawned closure SIGABRTs (exit 132) at cleanup. **FIXED (B4/E6).**

## Root Cause (diagnosed)

### B3 — Generator Runtime Crash (Rust-seed, OPEN)

HIR lowering of generator functions (`fn gen_counter(): yield 1`) is correct —
`HirExprKind::Yield` is emitted and the function lowers without error. The crash
(exit 132, SIGABRT) occurs in the **runtime interpreter** when executing yield
expressions. HIR-level tests in `hir::lower::tests::async_desugar_tests` confirm
lowering succeeds.

Minimal repro (after S6 fix):
```
fn gen_counter():
    yield 1
    yield 2
# → binary exits 132 (SIGABRT in interpreter executor during yield execution)
```

Fix required: in the interpreter execution layer (`src/compiler_rust/compiler/src/interpreter/`),
handle `HirExprKind::Yield` correctly — set up generator state machine context
before executing function body so yield doesn't abort. Authorized Rust change only.

### B3b — Actor HIR Scope Visibility (Rust-seed) — FIXED IN SEED (S6, 2026-06-11)

**Fixed (S6 seed batch, 2026-06-11, pending redeploy).**

Root cause: `Node::Actor` was missing from two places in
`src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs`:
1. Pass 0 (pre-registration loop): actor name was never registered as a placeholder `HirType::Struct`
2. `register_declarations_from_node`: `Node::Actor` arm was absent so `register_class` was never called

Both `lower_module` and `lower_module_with_warnings` paths now handle `Node::Actor` in Pass 0
(empty struct placeholder) and `register_declarations_from_node` (full field registration via
`register_class` with `fields: a.fields.clone()`). Method return types and function lowering
also extended for actor methods.

Before fix: `actor Counter: val count: i64` → runtime "symbol lookup fails for Counter as a class".
After fix (verified on release binary built 2026-06-11 16:30): exits 0, type registered in HIR.

Note: `Counter { count: 0 }` constructor instantiation produces "cannot infer field type" — this is
a **pre-existing bug** affecting structs equally (not introduced by this fix). Filed separately.

Regression tests added: `src/compiler_rust/compiler/src/hir/lower/tests/async_desugar_tests.rs`
(5 tests — all green):
- `test_generator_fn_lowers_without_unknown_variable`
- `test_gen_variable_name_resolves`
- `test_actor_type_visible_in_hir_scope`
- `test_actor_methods_lowered_to_hir`
- `test_actor_usable_after_declaration`

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

### B6 — HIR Hardcodes I64 for Await Result Type (Rust-seed) — FIXED IN SEED

**Fixed (S5 seed batch, 2026-06-11, pending redeploy).**

`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs` — was:
```rust
Expr::Await(inner) => {
    let future_hir = Box::new(self.lower_expr(inner, ctx)?);
    Ok(HirExpr {
        kind: HirExprKind::Await(future_hir),
        ty: TypeId::I64,   // ← was hardcoded, ignores operand type
    })
}
```
Now fixed to:
```rust
Expr::Await(inner) => {
    let future_hir = Box::new(self.lower_expr(inner, ctx)?);
    let operand_ty = future_hir.ty;
    Ok(HirExpr {
        kind: HirExprKind::Await(future_hir),
        ty: operand_ty,   // propagates operand type (eager-async identity)
    })
}
```
Simple async is EAGER: await on a non-Future is identity, so operand type is correct.
When `Future<T>` representation is added to the type system, this site must be
updated to extract `T` from the Future type. Regression tests added:
`test_await_expr_type_propagates_operand_type` and `test_await_expr_string_type_propagates`
in `hir/lower/tests/expression_tests.rs` (both green).

## Required Fix (prioritized)

1. **(DONE)** Guard `rt_future_await` against non-`FutureValue` input → typed error
   (removes the SIGSEGV class).
2. **(DONE)** Interpreter `Expr::Await` passthrough for non-Future values.
3. **(FIXED IN SEED — B3b, pending redeploy)** Register `Node::Actor` in HIR Pass 0 + `register_declarations_from_node` (S6: `module_pass.rs` +85 lines; 5 regression tests green).
3b. **(OPEN — Rust)** Fix interpreter executor to handle `HirExprKind::Yield` in generator functions without SIGABRT (B3 — separate from B3b).
4. **(OPEN — Rust)** Reconcile Promise vs FutureValue in the interpreter dispatch path (B5).
5. **(FIXED IN SEED — pending redeploy)** Propagate the real operand type for `await` (B6): `ty: TypeId::I64` → `ty: operand_ty` in `hir/lower/expr/mod.rs`. When Future<T> representation is added, this site must extract T instead.

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
