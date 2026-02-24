# Type System Roadmap

**Date:** 2026-02-24
**Status:** Master Plan
**Based on:** Cross-language research (Rust, Swift, TypeScript, Kotlin, Haskell, OCaml, Scala 3)

---

## Current State (as of 2026-02-24)

### Completed

| Feature | Status | Files |
|---------|--------|-------|
| HM Algorithm W + Robinson Unification | Done | `30.types/type_infer/core.spl` |
| Level-based generalization + let-polymorphism | Done | `30.types/type_infer/generalization.spl` |
| Type schemes, instantiation, substitution | Done | `30.types/type_infer_types.spl` |
| Function/generic/compound type inference | Done | `30.types/type_infer/inference_expr.spl` |
| Tensor/dimension constraints | Done | `30.types/type_infer/dim_solver.spl` |
| Pipeline operators (`|>`, `>>`, `~>`, `//`) | Done | `30.types/type_infer/inference_expr.spl` |
| Trait system (def, impl, solver, coherence) | Done | `25.traits/` (12+ files) |
| Monomorphization + cache | Done | `40.mono/` (18 files) |
| Borrow checking + GC analysis | Done | `55.borrow/` |
| **Bidirectional type checking (Phases 1-3)** | **Just Done** | `inference_expr.spl`, `inference_control.spl` |

### Designed (docs ready, not implemented)

| Feature | Design Doc | Est. |
|---------|-----------|------|
| Flow-sensitive type narrowing | `doc/design/flow_sensitive_narrowing_design.md` | 10-14 days |
| Effect system integration | `doc/design/effect_system_integration_design.md` | 12-18 days |

### Planned (plans exist, not implemented)

| Feature | Plan Doc | Est. |
|---------|---------|------|
| Associated types | `doc/plan/associated_types_implementation_plan.md` | 8h |
| Higher-rank polymorphism | `doc/plan/higher_rank_polymorphism_implementation_plan.md` | 12h |
| Variance inference | `doc/plan/rust_feature_parity_roadmap.md` | 8h |
| Macro type checking | `doc/plan/macro_type_checking_implementation_plan.md` | 15h |

---

## Research-Informed Priorities

### What the research says

| Insight | Source | Impact on Simple |
|---------|--------|-----------------|
| Non-nullable by default + `T?` syntax | Kotlin | Already have `Optional(T)` -- need narrowing |
| Flow-sensitive narrowing on `val` only | Kotlin, TypeScript | Soundness without complexity (use `Symbol.is_mutable`) |
| Declaration-site variance (`in`/`out`) | Kotlin, Scala 3 | Better than use-site, declare once on type def |
| Bidirectional inference over full HM | Rust, Swift | Just implemented -- local inference + signatures at boundaries |
| Associated types in traits | Rust, Haskell, Scala 3 | Essential for Iterator/Collection traits |
| Effect tracking as type-level concept | Kotlin (`suspend`), OCaml 5 | `async` as effect, not just syntax sugar |
| Union types for error/data modeling | TypeScript, Scala 3 | Add `Union` to `HirTypeKind` during narrowing work |
| Sealed hierarchies for exhaustive matching | Kotlin, Scala 3 | Extends existing enum system |
| Opaque types (zero-cost newtypes) | Scala 3, Rust | Module-scoped transparency |
| GATs over full HKTs | Rust, Haskell | Covers most use cases, less complexity |
| Gradual enforcement | TypeScript (`strict`), Kotlin | Warnings first, errors with flag |

---

## Roadmap: 6 Milestones

### Milestone 1: Bidirectional Testing + Bidir Polish (P0, ~3 days)

**Status:** Ready to start
**Depends on:** Bidirectional implementation (done)
**Goal:** Verify and polish the bidirectional type checking implementation.

| Task | Est. | Details |
|------|------|---------|
| 1.1 Write bidirectional test suite | 4h | `test/compiler/bidir_type_check_spec.spl` -- lambda inference, subsumption, return checking |
| 1.2 Run full test suite, fix regressions | 4h | Ensure no existing tests broken by new `infer_expr(expr, mode)` |
| 1.3 Bidir for list comprehensions | 4h | `val evens: [i64] = [for x in 0..10: x]` propagates element type |
| 1.4 Bidir for match arms | 4h | Expected type propagates into all match arm bodies |
| 1.5 Variance-aware subsumption | 4h | Replace `subsume()` with variance check (covariant containers, contravariant params) |

**Deliverable:** Bidirectional type checking fully tested and polished.

---

### Milestone 2: Flow-Sensitive Type Narrowing (P0, ~12 days)

**Status:** Design complete
**Depends on:** Milestone 1 (for bidirectional integration)
**Design:** `doc/design/flow_sensitive_narrowing_design.md`
**Goal:** Smart casts for `val` bindings after nil checks, `is` checks, `.?` checks.

| Task | Est. | Details |
|------|------|---------|
| 2.1 Core narrowing infrastructure | 2-3d | `NarrowingFact`, `NarrowingCondition`, `NarrowingContext` in `35.semantics/narrowing.spl`; add `narrowing` field to `HmInferContext` |
| 2.2 Nil-check narrowing | 2d | `if x != nil:` / `if x.?:` narrows `T?` to `T` for `val` bindings |
| 2.3 Early-return narrowing | 2d | `if x == nil: return` narrows remainder; `definitely_terminates()` analysis |
| 2.4 `is` type check narrowing | 2d | `if x is text:` narrows in then-branch; requires union type support |
| 2.5 Add `Union` to HirTypeKind | 2d | `Union(members: [HirType])`, unification rules, lowering from parser |
| 2.6 `and`/`or` chain narrowing | 1d | `if x != nil and y != nil:` narrows both |
| 2.7 Match arm scrutinee narrowing | 1d | Scrutinee variable narrowed within each arm body |

**Deliverable:** Smart casts working for optionals and union types on `val` bindings.

---

### Milestone 3: Associated Types (P1, ~8 days)

**Status:** Plan complete
**Depends on:** Milestone 1 (bidirectional for type-level check mode)
**Plan:** `doc/plan/associated_types_implementation_plan.md`
**Goal:** `trait Iterator { type Item; fn next() -> Item? }` with projection `I.Item`.

| Task | Est. | Details |
|------|------|---------|
| 3.1 AssocTypeDef + TraitDef extension | 2d | `AssocTypeDef` class, extend `TraitDef.assoc_types`, built-in Iterator |
| 3.2 AssocTypeImpl + ImplBlock extension | 2d | `AssocTypeImpl`, validation (completeness, bounds), `impl Iterator for Range { type Item = i64 }` |
| 3.3 Type projection + resolution | 2.5d | `AssocTypeProjection`, `AssocTypeResolver`, `Projection` in `HirTypeKind`, normalization |
| 3.4 TraitSolver + method resolution | 1.5d | Associated type constraints in obligations, method resolution with projections |

**Deliverable:** `fn sum<I: Iterator>(iter: I) -> I.Item` compiles and resolves.

---

### Milestone 4: Effect System Integration (P1, ~14 days)

**Status:** Design complete
**Depends on:** Milestone 1 (bidirectional for effect checking)
**Design:** `doc/design/effect_system_integration_design.md`
**Goal:** Wire existing 2,000+ lines of effect infrastructure into the compilation pipeline.

| Task | Est. | Details |
|------|------|---------|
| 4.1 Unify effect types | 1-2d | Eliminate 4 duplicate `Effect` enums, use `hir_types.spl` `EffectKind` everywhere |
| 4.2 Wire into pipeline | 2-3d | `effect_pass.spl` coordinator, call from `driver.spl` after HIR lowering |
| 4.3 Populate function type effects | 2-3d | `HirTypeKind.Function.effects` populated during inference, lambda body effects |
| 4.4 Async-from-sync checking | 1-2d | Warning when calling async from sync context, `--strict-effects` flag |
| 4.5 Promise wrapping + await inference | 2-3d | Auto-wrap async return types to `Promise<T>`, `~` operator type checking |
| 4.6 IO/Mutates/Allocates tracking | 2-3d | Extended effect kinds, `@pure` annotation enforcement |
| 4.7 Incremental caching | 1-2d | Wire `EffectCache`, invalidation on change |

**Deliverable:** `async fn` produces `[Async]` effect, sync-calls-async warns, `~` types correctly.

---

### Milestone 5: Variance + Higher-Rank + Opaque Types (P2, ~12 days)

**Status:** Plans exist
**Depends on:** Milestones 2-3 (narrowing + associated types)
**Goal:** Advanced type system features from Rust/Kotlin/Scala 3.

| Task | Est. | Details |
|------|------|---------|
| 5.1 Declaration-site variance | 4d | `in`/`out` modifiers on generic params, variance checking on type defs, covariant `List<out T>` vs invariant `MutableList<T>` |
| 5.2 Higher-rank polymorphism | 5d | `for<'a>` / `forall` nested in function types, rank-2 for safe encapsulation (ST-monad pattern) |
| 5.3 Opaque types | 3d | `opaque type Log = f64` -- transparent within defining module, abstract outside, zero runtime cost |

**Deliverable:** Variance-safe generics, higher-rank callbacks, zero-cost newtypes.

---

### Milestone 6: GATs + Match Types + Sealed Extensions (P3, ~10 days)

**Status:** Future
**Depends on:** Milestones 3, 5
**Goal:** Advanced type-level features.

| Task | Est. | Details |
|------|------|---------|
| 6.1 GATs (Generic Associated Types) | 4d | `type Iter<'a>: Iterator<Item=&'a Self.Item>`, subsumes most HKT use cases |
| 6.2 Match types (conditional types) | 3d | `type Elem<X> = X match { case Array<T>: T; case text: u8 }` -- type-level pattern matching |
| 6.3 Sealed interface extensions | 3d | `sealed trait Shape` with exhaustive `when`/`match`, cross-module sealed hierarchies |

**Deliverable:** Type-level programming, GAT-based generic abstractions.

---

## Dependency Graph

```
M1: Bidir Testing + Polish
 |
 +-----> M2: Flow-Sensitive Narrowing
 |         |
 |         +-----> M5: Variance + Higher-Rank + Opaque
 |                   |
 +-----> M3: Associated Types ---------> M6: GATs + Match Types + Sealed
 |         |
 +-----> M4: Effect System Integration
```

M1 is the foundation. M2, M3, M4 can proceed in parallel after M1. M5 depends on M2+M3. M6 depends on M3+M5.

---

## Timeline

| Milestone | Est. Duration | Cumulative | Priority |
|-----------|--------------|------------|----------|
| M1: Bidir Polish | 3 days | Week 1 | P0 |
| M2: Flow Narrowing | 12 days | Weeks 2-3 | P0 |
| M3: Associated Types | 8 days | Weeks 2-3 (parallel with M2) | P1 |
| M4: Effect System | 14 days | Weeks 2-4 (parallel with M2/M3) | P1 |
| M5: Variance + HRP + Opaque | 12 days | Weeks 5-6 | P2 |
| M6: GATs + Match Types | 10 days | Weeks 7-8 | P3 |
| **Total** | **~59 days** | **~8 weeks** | |

With 3 milestones running in parallel (M2/M3/M4), the critical path is:

```
M1 (3d) -> M2 (12d) -> M5 (12d) -> M6 (10d) = 37 days critical path
```

---

## Key Design Decisions (from research)

### 1. Inference Strategy: Local Bidirectional (not full HM)

**Adopted from:** Rust, Swift
**Rejected:** Haskell's complete HM (error messages too far from bug site)

Require type annotations at function boundaries. Infer everything inside function bodies using bidirectional propagation. This is already implemented.

### 2. Narrowing: Val-Only (Kotlin's approach)

**Adopted from:** Kotlin
**Rejected:** TypeScript's approach (unsound for concurrent/mutable contexts)

Only narrow immutable `val` bindings. Use existing `Symbol.is_mutable` field. Sound without escape analysis.

### 3. Effect System: Type-Level Effects with Gradual Enforcement

**Adopted from:** Kotlin (`suspend`), OCaml 5 (algebraic effects), Lean 4 (formal model)
**Rejected:** Haskell monads (composition problem), full algebraic effects (too complex initially)

Start with `Async`/`Pure`, enforce as warnings, add `--strict-effects` for errors. Expand to `IO`/`Mutates`/`Allocates`/`Throws` later.

### 4. Variance: Declaration-Site (Kotlin's `in`/`out`)

**Adopted from:** Kotlin, Scala 3
**Rejected:** Java's use-site wildcard (`? extends T`)

Declare variance on the type definition, not at every use site. Compiler enforces position constraints.

### 5. Type Abstraction: Opaque Types (Scala 3 model)

**Adopted from:** Scala 3
**Rejected:** Full path-dependent types (too complex), wrapper classes (runtime cost)

`opaque type UserId = i64` -- transparent inside module, abstract outside, zero cost.

### 6. Generics: GATs over HKTs

**Adopted from:** Rust (stabilized 1.65)
**Rejected:** Full HKTs (complicates monomorphization)

GATs cover most HKT use cases (Functor, Monad abstractions) with less type system complexity.

### 7. Union Types: First-Class in HIR

**Adopted from:** TypeScript, Scala 3
**Implementation:** Add `Union(members: [HirType])` to `HirTypeKind`

Enables `fn parse(s: text) -> i64 | ParseError` and flow-sensitive narrowing with `is` checks.

---

## Files Affected (Summary)

### New Files

| File | Milestone | Purpose |
|------|-----------|---------|
| `src/compiler/35.semantics/narrowing.spl` | M2 | NarrowingFact, NarrowingContext, condition analysis |
| `src/compiler/25.traits/associated_types.spl` | M3 | AssocTypeProjection, AssocTypeResolver |
| `src/compiler/30.types/type_system/effect_pass.spl` | M4 | Effect inference pass coordinator |
| `test/compiler/bidir_type_check_spec.spl` | M1 | Bidirectional tests |
| `test/compiler/narrowing_spec.spl` | M2 | Narrowing tests |

### Modified Files

| File | Milestones | Changes |
|------|-----------|---------|
| `30.types/type_infer/inference_expr.spl` | M1-M4 | Bidir polish, narrowing in `If`, effect propagation in `Call` |
| `30.types/type_infer/inference_control.spl` | M1-M2 | Narrowing scope push/pop, early-return promotion |
| `30.types/type_infer.spl` | M2 | Add `narrowing: NarrowingContext` to `HmInferContext` |
| `30.types/type_infer/context.spl` | M2 | Modified `lookup` to check narrowing context first |
| `20.hir/hir_types.spl` | M2, M5 | Add `Union` variant, variance annotations |
| `20.hir/hir_lowering/items.spl` | M4 | Populate `effects` from `is_async` annotation |
| `25.traits/trait_def.spl` | M3 | Add `assoc_types` to `TraitDef` |
| `25.traits/trait_impl.spl` | M3 | Add `assoc_type_impls` to `ImplBlock` |
| `25.traits/trait_solver.spl` | M3 | Associated type constraints in obligations |
| `80.driver/driver.spl` | M4 | Insert effect pass between HIR lowering and type checking |

---

## Success Criteria

| Milestone | Key Metric |
|-----------|-----------|
| M1 | `\x: x * 2` infers `x: i64` from `fn(i64) -> i64` context; all existing tests pass |
| M2 | `if x != nil: x + 1` compiles without `.unwrap()` for `val x: i64?` |
| M3 | `fn sum<I: Iterator>(iter: I) -> I.Item` resolves `I.Item` to concrete type |
| M4 | `async fn` calling sync is OK; sync calling async warns; `~` on non-Promise errors |
| M5 | `List<Dog>` assignable to `List<Animal>` (covariant); `opaque type Id = i64` works |
| M6 | `trait Collection { type Iter<'a> }` compiles; `type Elem<X> = X match { ... }` evaluates |

---

## Implementation Order for Multi-Agent Execution

When implementing with multiple parallel agents:

**Wave 1 (sequential):** M1 -- must complete first as foundation
**Wave 2 (parallel):** M2 + M3 + M4 -- independent after M1
**Wave 3 (sequential after M2+M3):** M5
**Wave 4 (sequential after M3+M5):** M6

Each milestone can be assigned to a dedicated agent with its own design doc for context.
