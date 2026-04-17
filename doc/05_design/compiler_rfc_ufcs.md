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
