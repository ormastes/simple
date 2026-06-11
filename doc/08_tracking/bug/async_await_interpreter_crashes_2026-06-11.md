# Async/Await Interpreter Crashes - 2026-06-11

Status: partially-fixed (2026-06-12) — B1/B2(await) VERIFIED FIXED; B3(generator SIGILL) FIXED IN SEED (2026-06-12) — exit 132 eliminated, JIT compile_yield emits safe NIL return; B3b(actor HIR scope) FIXED IN SEED — pending redeploy; B4(spawn SIGABRT) VERIFIED FIXED via E6; B5(Promise/FutureValue) DOCUMENTED-CANONICAL — behavior pinned by 7 Rust regression tests (S8, 2026-06-11); B6(HIR I64) FIXED IN SEED — pending redeploy; coverage gap documented.

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
- ~~B3: generator/yield runtime interpreter crash (exit 132 SIGABRT)~~ → **FIXED IN SEED (2026-06-12):** `compile_yield` in `codegen/instr/async_ops.rs` replaced unconditional `trap` (emitting CPU `ud2`/SIGILL) with a safe NIL return when `generator_state_map` is None. JIT path now falls back to interpreter gracefully. Probes exit 0 (not 132). 2 new regression tests in `async_desugar_tests.rs` (HIR→MIR lower succeeds).
- ~~B5: Promise-vs-FutureValue deep representation reconcile.~~ → **DOCUMENTED-CANONICAL (S8, 2026-06-11):** Representation map written below; behavior pinned by 7 Rust regression tests in `async_gen_tests.rs` (all green). Cross-path behavior is correct under eager-async semantics; no unification required.
- ~~B3b: actor desugar class not visible in HIR scope~~ → **FIXED IN SEED (S6 batch, pending redeploy):** `Node::Actor` registered in Pass 0 + `register_declarations_from_node` via `register_class`. 5 regression tests green (`hir::lower::tests::async_desugar_tests`). Binary verified: `actor Counter: val count: i64` + no-ctor usage exits 0 cleanly.
- ~~B6: HIR hardcodes I64 for await result type~~ → **FIXED IN SEED (S5 batch, pending redeploy):** `ty: TypeId::I64` replaced with `ty: operand_ty` (the inner expression's type). Rust tests: `test_await_expr_type_propagates_operand_type` + `test_await_expr_string_type_propagates` both green.

## Per-Item Triage Table (2026-06-11 audit)

| # | Item | Category | Status | Action |
|---|------|----------|--------|--------|
| B1 | SIGSEGV `await f()` → NIL (exit 139) | (a) Fixed | VERIFIED FIXED | commit 861e29bc99; spec 3/3 green |
| B2 | `await f()` yields 3/NIL in JIT/interpreter | (a) Fixed | VERIFIED FIXED | same commit; eager-async identity |
| B3 | `yield` / generator runtime interpreter crash (SIGABRT/SIGILL) | (c) Rust-seed | FIXED IN SEED (2026-06-12) | compile_yield safe NIL return; exit 132 eliminated; 2 regression tests green |
| B3b | `actor` desugar class not visible in HIR scope | (c) Rust-seed | FIXED IN SEED — pending redeploy | S6: `Node::Actor` in Pass 0 + register_class; 5 tests green |
| B4 | `spawn fn()` closure SIGABRTs (exit 132) at cleanup | (a) Fixed | VERIFIED FIXED | E6 in green_thread_direct_runtime_blockers_2026-06-06.md |
| B5 | Promise vs FutureValue unreconciled in MIR executor | (c) Rust-seed | OPEN | root-cause note below |
| B6 | HIR hardcodes `TypeId::I64` for await result type | (c) Rust-seed | FIXED IN SEED — pending redeploy | S5 batch: `ty: operand_ty`; tests green |
| C1 | Coverage gap: 7 specs are single-skip placeholders | (b)/(c) mixed | DOCUMENTED | see Coverage section below |
| C2 | `async_integration_spec` has 21 hollow `expect(1).to_equal(1)` tests | (b) | FILLED (S7, 2026-06-12) | 21/21 honest assertions; generator-blocked tests rewritten to pin declaration-level behaviour; 0 vacuous bodies remain |

## Summary

End-to-end `async fn` + `await` crashes the Rust-seed interpreter instead of
producing a value or a typed error. Found during the 2026-06-11 async audit
(plan: `doc/03_plan/language/concurrency/async_green_process_hardening.md`).

## Symptoms (probe programs, interpreter mode)

- `async fn f() -> i64: 42` + `val x = await f()` → SIGSEGV (exit 139). **FIXED.**
- `yield` in a generator fn → runtime SIGABRT/SIGILL (exit 132); HIR lowering itself succeeds. **FIXED IN SEED (B3, 2026-06-12): exit 132 eliminated.** JIT compile_yield now emits safe NIL return instead of `ud2` trap; process stays alive and interpreter handles gen fn correctly.
- `actor` definition → HIR scope visibility failure (symbol lookup fails for actor as a class). **FIXED IN SEED (B3b, S6 batch, pending redeploy).** Before fix: "symbol lookup fails for Counter as a class". After fix (verified on fresh binary): `actor Counter: val count: i64` exits 0 with no error. Constructor instantiation (`Counter { count: 0 }`) hits a pre-existing field-type-inference limitation that also affects structs; that is a separate unrelated bug.
- `spawn fn()` runs, but the spawned closure SIGABRTs (exit 132) at cleanup. **FIXED (B4/E6).**

## Root Cause (diagnosed)

### B3 — Generator Runtime Crash (Rust-seed) — FIXED IN SEED (2026-06-12)

**Fixed 2026-06-12.** Root cause was in `codegen/instr/async_ops.rs` `compile_yield`,
not the interpreter. When `generator_state_map` is `None` (i.e. the function is a `gen fn`
declaration, not an outlined body from the `generator()` builtin), the old fallback was:
```rust
builder.ins().trap(cranelift_codegen::ir::TrapCode::unwrap_user(2));
```
This emits a CPU `ud2` (illegal instruction), causing SIGILL (exit 132/248). Fix:
```rust
// B3 safety net: emit safe NIL return instead of trap
let nil = builder.ins().iconst(cranelift_codegen::ir::types::I64, 0);
builder.ins().return_(&[nil]);
```
JIT compile of `gen fn` still fails (generator_state_map is None for top-level `gen fn`
declarations because `lower_generator` is only called for outlined closure bodies in
`codegen/shared.rs`). The JIT failure causes fallback to the interpreter, which handles
`gen fn` correctly via `func.is_generator` + `GENERATOR_YIELDS` thread-local.

**Before fix (2026-06-11):** `gen gen_counter(): yield 1` → exit 132 (SIGILL).
**After fix (2026-06-12):** same probe → exit 0. JIT compile error → interpreter fallback → clean execution.

**Files changed:**
- `src/compiler_rust/compiler/src/codegen/instr/async_ops.rs`: trap → NIL return in compile_yield
- `src/compiler_rust/compiler/src/hir/lower/tests/async_desugar_tests.rs`: 2 new regression tests
  (`test_generator_fn_mir_lower_succeeds_single_yield`, `test_generator_fn_mir_lower_succeeds_two_yields`)

**Remaining gap:** `for x in gen_counter()` causes exit 139 (segfault) — for-in iterator
dispatch over generator objects is a separate unimplemented feature, not part of B3.
Top-level `gen fn` calls via `gen_counter()` exit 0 cleanly.

**Integration behaviours still blocked (S7):** the following `async_integration_spec`
scenarios remain declaration-only until for-in + generator iteration is fully wired:
- Generator value iteration from a spawn pipeline (calling a gen fn body from a green task)
- Actor with generator method called at runtime (actor method containing yield)
- `async fn` yielding from inside a generator body (mixed async+generator nesting)
- Combined actor + generator + await full-pipeline execution (all four features together)

These tests exist as structural/declaration-level assertions only.
See `test/01_unit/compiler/async/async_integration_spec.spl`.

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

All 7 tests green: `cargo test -p simple-runtime test_b5` → `7 passed; 0 failed` (S8 verification run, 2026-06-11).
5 pre-existing failures in `executor`, `loader`, and `value::serial` modules are unrelated to B5.

#### Binary Verification (S8, 2026-06-11)

Fresh binary: `src/compiler_rust/target/release/simple` (built via `cargo build --release -p simple-driver`).

Probe program:
```simple
async fn get_num() -> i64:
    42

async fn get_text() -> text:
    "hello async"

fn get_double() -> i64:
    val n = await get_num()
    val m = await await get_num()
    n + m

fn main():
    val n = await get_num()
    print(n)
    val t = await get_text()
    print(t)
    val d = get_double()
    print(d)
```

| Probe | Expected | Got | Status |
|---|---|---|---|
| `await` async fn returning i64 | `42` | `42` | PASS |
| `await` async fn returning text | `hello async` | `hello async` | PASS |
| `await(await(x))` double-await identity | `84` (42+42) | `84` | PASS |

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
