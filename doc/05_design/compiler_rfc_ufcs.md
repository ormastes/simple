# Compiler RFC: Uniform Function Call Syntax (UFCS)

**Status:** Proposed
**Created:** 2026-04-17
**Track:** Phase 9 — Compiler RFC Track
**Related:** `doc/05_design/ui_typed_core_rfc.md` §4.2, §9
**See also:** `doc/05_design/compiler_rfc_bare_enum_literals.md`, `doc/05_design/compiler_rfc_method_chain_fix.md`
**Prior art:** `doc/05_design/ufcs_dot_operator_design.md` (earlier design, status: Complete — but UI phases reveal the feature is not yet usable in practice for library ergonomics)

---

## 1. Motivation

Today, `with_width(node, 120)` works; `node.width(120)` requires defining a real method on the type. Library authors who want dot-chain ergonomics must duplicate every helper: a free function form (`with_padding_token`) **and** a method form (`padding`). The Simple UI library paid this cost in Phases 3, 4, 5, and 6 — roughly 50+ duplicate definitions.

Without UFCS:
```simple
# Must define both:
fn with_width(node: WidgetNode, w: Int) -> WidgetNode: ...   # free function
me width(self: WidgetNode, w: Int) -> WidgetNode: ...         # method duplicate
```

With UFCS, one definition serves both call sites. The library defines only the free-function form; callers use whichever syntax reads better.

---

## 2. Proposed Design

### 2.1 Resolution rule

When the compiler resolves `expr.fn_name(args)` and **no method** `fn_name` exists on `expr`'s type (no class method, no trait implementation), fall back to free-function lookup:

1. Search in-scope free functions named `fn_name` where the first parameter type is compatible with `expr`'s type.
2. If exactly one match is found, desugar `expr.fn_name(args)` → `fn_name(expr, args)`.
3. If no match is found, emit the normal "method not found" error.

### 2.2 Resolution priority (strict order)

| Priority | Source |
|----------|--------|
| 1 | Class method (`me fn_name`) on the receiver's type |
| 2 | Trait method implemented for the receiver's type |
| 3 | Free function `fn_name(receiver_type, ...)` in scope |

Existing method calls are **never affected**. UFCS only fires when no method exists.

### 2.3 Desugar rule

Pure syntactic rewrite at typecheck-resolution time. No IR change, no runtime cost. The HIR produced by `expr.fn_name(args)` via UFCS is identical to the HIR produced by `fn_name(expr, args)` directly.

---

## 3. Edge Cases

**Ambiguity — method and free function both exist:** Method wins (priority 1 > priority 3). Current behavior is preserved.

**Multiple free functions with the same name:** Existing overload-resolution rules apply. If they resolve ambiguously on the first argument type, emit an "ambiguous UFCS candidate" diagnostic listing all candidates. User must either qualify or rename.

**Operator overloading:** Out of scope. `+`, `-`, `*`, `/`, `==`, etc. are not affected; those go through the operator trait path.

**Chained calls:** UFCS resolution is per-call-site. `expr.a().b()` resolves `a` first; if that returns a type, `b` is resolved on that return type. No special handling needed beyond fixing the chain bug (see `doc/05_design/compiler_rfc_method_chain_fix.md`).

**Generic free functions:** Supported. Type inference on the first parameter proceeds as normal; the remaining type parameters are inferred from `args`.

---

## 4. Compatibility

Strictly additive. No existing code changes meaning:
- `node.width(120)` where `width` is a real method → unchanged (priority 1).
- `with_width(node, 120)` free-function call → unchanged.
- `node.width(120)` where `width` has no method but a free function `width(WidgetNode, Int)` exists → now resolves via UFCS (previously was a compile error).

---

## 5. Implementation Pointer

Target: **`src/compiler/30.types/`** — the type/resolution layer, specifically the method-call resolution path in `bidirectional_checking.spl` and the type inference entry points. The HIR `MethodCall` node already carries a `resolved` field (per `ufcs_dot_operator_design.md`); UFCS fills that field with a `FreeFunctionTarget` variant when no class/trait method is found.

If the prior `ufcs_dot_operator_design.md` design is already partially wired, the implementer should audit whether `FreeFunctionTarget` resolution is actually exercised in practice against UI library call sites. The Phase 3–6 duplicate definitions suggest it is not.

Secondary touch: **`src/compiler/35.semantics/`** — any name-lookup scope walk that needs to surface free functions as UFCS candidates.

---

## 6. Migration Impact

Once landed:
- The `with_*` free-function helpers added in Phases 3, 4, 5, 6 of the UI migration become redundant. The method form (`width`, `height`, `accent`, `padding`, etc.) becomes canonical.
- A one-time cleanup pass deletes the `with_*` duplicates from `src/lib/common/ui/builder.spl` and related files.
- No call-site changes required — existing `with_*` callers continue to work unchanged (they call the free function directly, bypassing UFCS).

Risk 7 from `ui_typed_core_rfc.md` ("two API styles confuse users") is fully resolved once the `with_*` legacy forms are removed post-UFCS landing.

---

## 7. Acceptance Criteria

- `node.width(120)` compiles and runs when only a free function `fn width(node: WidgetNode, w: Int) -> WidgetNode` exists.
- `node.width(120).height(40)` works (conditional on `compiler_rfc_method_chain_fix.md` landing first).
- No existing test regresses.
- "method not found" errors still emit correctly when neither a method nor a compatible free function exists.
- Ambiguity diagnostic fires when two free functions match the first-arg type.

---

### Audit findings (Phase 9 investigation 2026-04-17)

#### 1. What `ufcs_dot_operator_design.md` claimed shipped

The design (Status: "Complete") describes resolution-time UFCS: `x.method(args)` tries (1) instance method, (2) trait method, (3) free function where first param matches receiver type. The `MethodResolution` enum with `FreeFunction(func_id)` variant was added to HIR; a `MethodResolver` class with `try_ufcs` was written; the interpreter at `src/compiler/70.backend/backend/interpreter.spl:186-187` handles `FreeFunction`. The pipeline step at `src/compiler/80.driver/driver.spl:459-460` calls `resolve_methods(hir_module)` labeled "Step 2: Method resolution (UFCS)".

#### 2. What is actually implemented

**`src/compiler/35.semantics/resolve.spl:572-595`** — the public entry point `resolve_methods()` (and `resolve_methods_with_solver()`) is a two-line stub:

```
fn resolve_methods(module: HirModule) -> (HirModule, [ResolveError]):
    # Bootstrap fallback: skip UFCS resolution until self-host runtime
    # supports the full MethodResolver method surface.
    (module, [])
```

Every `MethodCall` node stays at `MethodResolution.Unresolved` (set by HIR lowering at `src/compiler/20.hir/hir_lowering/expressions.spl:105`). The `MethodResolver` class and `try_ufcs` strategy in `resolve_strategies.spl` are fully written but never called.

The **Rust seed compiler** (`src/compiler_rust/`) has its own independent method-call path in `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:lower_method_call`. Its codegen (`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:compile_method_call_static`) resolves method names by suffix search over `func_ids` — finding any registered function whose mangled name ends with `_dot_<method>`. This is a weaker, name-only heuristic: it finds `foo.bar()` → `SomeType_dot_bar` regardless of first-parameter type. It does NOT perform the `try_ufcs` type-compatibility check.

#### 3. Concrete counterexample

```simple
# test/ufcs_audit_repro.spl  (runs inside project tree)
use common.ui.widget.{WidgetNode}
use common.ui.builder.{with_padding_token}
use common.ui.design_tokens.{Spacing}
use common.ui.theme_registry.{ThemeId}

fn test_ufcs_cross_module():
    val n = WidgetNode(id: "x")
    # padding_token is NOT a method on WidgetNode.
    # True UFCS would resolve to: with_padding_token(n, ThemeId.IOSLight, Spacing.Md)
    val n2 = n.padding_token(ThemeId.IOSLight, Spacing.Md)
```

**Result:** `bin/simple compile test/ufcs_audit_repro.spl` succeeds, but NOT via UFCS. The Rust seed suffix-search finds any function whose mangled name ends with `_dot_padding_token`. Since `with_padding_token` does NOT end in `_dot_padding_token`, no suffix match is found — the compile may emit an unresolved call or silently produce incorrect codegen (not verified at runtime). The self-hosted Simple compiler path will emit `MethodResolution.Unresolved` and produce a runtime/codegen error once the stub is removed.

The method duplicates (`fn padding`, `fn width`, `fn height`, `fn accent` on `WidgetNode`) are needed specifically because:
- The Rust seed suffix heuristic cannot correctly resolve `n.padding_token(...)` → `with_padding_token(...)` (different prefix).
- The self-hosted path stubs out `resolve_methods` entirely.
- `WidgetNode.padding` at `widget.spl:700` is itself a wrapper that calls `with_padding_token(self, theme, s)`.

#### 4. Hypothesis — why UFCS is skipped

Root cause: **bootstrap deadlock stub**. The comment in `resolve.spl:578` says "skip UFCS resolution until self-host runtime supports the full MethodResolver method surface." The `MethodResolver` calls into `SymbolTable`, `TypeChecker`, `TraitSolver` — types that may not yet be bootstrappable. Rather than risk a broken self-hosted build, the pass was stubbed out. The design doc was marked "Complete" when the infrastructure (enum, class, strategies) was written, before the entry point was un-stubbed and tested end-to-end.

The `infer_method_call` in `src/compiler/30.types/type_system/expr_infer_calls.spl` also lacks UFCS: it returns a fresh type variable for all method calls (`Ok(engine_fresh_var(engine))`), so type inference never errors on `n.padding_token(...)` either — it defers resolution downstream to the stubbed pass.

#### 5. Concrete fix

**File:** `src/compiler/35.semantics/resolve.spl`, lines 572–581.

Replace the stub body with the actual resolver call:

```
fn resolve_methods(module: HirModule) -> (HirModule, [ResolveError]):
    val resolver = create_method_resolver(module.symbols)
    resolver.build_trait_impls(module.impls)
    val resolved = resolver.resolve_module(module)
    (resolved, resolver.errors)
```

Secondary: `infer_method_call` in `src/compiler/30.types/type_system/expr_infer_calls.spl` returns a fresh var for all method calls; after un-stubbing `resolve_methods`, UFCS errors will surface only at the resolve pass, not at type-inference time. That is acceptable for now.

**Fix complexity: small** — the resolver is fully implemented. The only change is replacing the two stub bodies in `resolve.spl:572-595`. The bootstrap concern needs a smoke test: compile the Simple compiler itself after un-stubbing to verify `MethodResolver` is bootstrappable.

#### 6. Status verdict

`ufcs_dot_operator_design.md` should be marked **"Partial — infrastructure complete, entry point stubbed (bootstrap blocker)"**. The "Complete" status is incorrect: the design was implemented as data structures and algorithms but was never activated in the compilation pipeline.

### Plumbing correction (Phase 9 follow-up 2026-04-18)

A first attempt at the un-stub revealed the fix is larger than "4 lines". `resolve_methods(module: HirModule)` (resolve.spl:572) does not currently receive a `SymbolTable`, but `MethodResolver.new(symbols: SymbolTable)` (resolve.spl:118) and `create_method_resolver(symbols: SymbolTable)` (resolve.spl:151) require one. To wire it correctly:

1. **Change `resolve_methods` signature** to `fn resolve_methods(module: HirModule, symbols: SymbolTable) -> (HirModule, [ResolveError])` — same for `resolve_methods_with_solver`.
2. **Update both call sites in `src/compiler/80.driver/driver.spl:460,591`** to pass a `SymbolTable`. The natural source is `self.ctx.symbols` (or whatever the context type's symbol-table accessor is named — needs verification).
3. **Confirm the populated `SymbolTable` actually contains the receiver type's methods** at the point `resolve_methods` is called, so the `try_method` strategy in `MethodResolver` returns hits instead of falling through to `try_ufcs`. If symbols aren't populated yet at that pass, the fix needs a different injection point.

Realistic scope: 20–30 line plumbing change touching `resolve.spl` (function signatures + body), `driver.spl` (two call sites), and any other internal callers of `resolve_methods`. Verification cost includes a Stage 4 self-host build (~16s) and confirming `bin/simple lint`, `bin/simple check`, and `bin/simple format` all stop emitting `Function 'X' not found` runtime errors from the 2419 stubbed-method paths.

**Empirical evidence**: Stage 4 succeeds in 16.3s with `EXIT=0` and produces a 27.5MB binary, but every command path that traverses methods (`lint`, `check`, `format`) fails with `Runtime error: Function 'level' not found` / `'line' not found`. The `test` command works because its hot path doesn't traverse the diagnostic-formatter's method calls. This confirms: the resolver stub is what's breaking — un-stubbing it (with the SymbolTable plumbed correctly) should fix all three commands in one shot.
