# Nested enum payload sub-patterns always-match and never-bind on the JIT

**Date:** 2026-08-01
**Status:** Fixed (one-level variant sub-patterns); residue filed below
**Engines:** JIT wrong. Tree-walk interpreter correct. Native gate-blocked (not wrong).
**Fixture:** `test/fixtures/compiler/nested_payload_subpattern_matrix.spl`

## Symptom

A nested payload sub-pattern such as `case Const(Inner.Str(name), _):` was
compiled as if the sub-pattern were a wildcard: the arm matched regardless of
the *inner* variant, and any binder inside it read zero.

```
case Const(Inner.Str(name), tag): name + tag   # selected even for Inner.Num
case Const(Inner.Num(v), tag):    v + tag + 500 # unreachable
```

Because specs run on the tree-walk interpreter, which recurses correctly
(`interpreter_patterns.rs:226`), **no spec caught this**.

## Measured shape matrix (before the fix)

| Shape | interpreter | JIT |
|---|---|---|
| `case Other(x)` single-level bind | correct | correct |
| multi-slot payload `T(a, b)` | correct | correct |
| struct payload `P(p)` | correct | correct |
| wildcard + bind `T(_, b)` | correct | correct |
| **nested variant `Const(Inner.Str(n), tag)`** | correct | **always matches, n = 0** |
| **nested variant, wildcard inner `Const(Inner.Str(_), tag)`** | correct | **always matches** |
| **literal in payload slot `A(0, y)`** | correct | **always matches** |
| **user enum with variants named `Some`/`None`** | correct | **`case Some(x)` irrefutable, x = 3** |

Native rejects every payload arm outright
(`compilability.rs::is_native_payload_free_enum_match`), so it was never
*wrong* — only gate-blocked.

## Reconciliation with the 2026-08-01 refutation (read this before citing either)

A parallel lane measured all 6 `WsFrame` variants plus a minimal 2-variant enum
on 2026-08-01 and reported that payload sub-patterns **bound correctly on both
the interpreter and the JIT**, refuting "the JIT is wrong". **That measurement
was correct and is not contradicted by this bug.** Both records stand:

* The failing axis is **nesting, not payloads**. Every shape that lane tested
  was single-level (`case Binary(payload)`, `case Close(code, reason)`), and
  single-level payload binds *are* correct on the JIT — see the first four rows
  of the matrix above, which reproduce that lane's result exactly.
* The defect needs a **variant pattern nested inside a payload slot**
  (`Const(Inner.Str(n), _)`). No `WsFrame` variant has that shape, so the lane
  could not have hit it.

Consequence: the isel/wasm workarounds that bound the constant in the outer arm
and destructured in a second top-level match **were justified**, not redundant.
Do not remove them by citing the refutation alone; the shape they avoid is the
nested one.

## Two distinct root causes

### 1. `Some`/`None` matched by NAME, not by type

`hir/lower/expr/control.rs` and its statement-form twin `hir/lower/stmt_lowering.rs`
short-circuited *any* pattern whose variant was spelled `Some`/`None` to
`rt_is_some`/`rt_is_none`. `rt_is_some` means "not the nil sentinel", which is
true for every value of a real enum — so for a user-defined
`enum UserOpt: Some(x); None`, `case Some(x)` was irrefutable and bound
`x = 3` (the nil tag).

**Fix:** compute `subject_enum_owns_variant` *before* the fast paths and gate
both on it. Built-in `T?` optionals are unaffected: their subject type is not
an Enum declaring those variant names.

### 2. The variant tag test never recursed into the payload

`lower_pattern_condition` matched `Pattern::Enum { name: _, variant, .. }` —
the `..` discarded `payload` — and emitted a single
`rt_enum_check_discriminant` for the outer tag only. Correspondingly
`build_pattern_binding_stmts` bound only `Pattern::Identifier`/`MutIdentifier`
payload slots, plus a nested-*struct* special case; a nested *enum variant*
fell through `if let Some(struct_info)` and emitted no initializer, leaving the
pre-registered local at its stack zero.

**Fix:** `nested_payload_condition` (control.rs) AND-s a discriminant test for
each refutable variant sub-pattern onto the outer tag test; a new branch in
`build_pattern_binding_stmts` unwraps `rt_enum_payload` twice (outer slot, then
inner payload) and emits the `Let` bindings.

Struct-vs-variant ambiguity is resolved by `is_real_enum_variant_name`: the
parser spells both `Shape.Circle(..)` and `Point(x, y)` as `Pattern::Enum`, and
emitting a discriminant check for the struct spelling would test an object
pointer's enum header and never match.

## Residue — still irrefutable in payload position (NOT fixed)

Filed rather than silently normalized:

1. **Literal sub-patterns** — `case A(0, y):` still matches any `A`. Measured
   on the fixed binary: `A(x: 9, y: 7)` against `case A(0, y)` returns 7 on the
   JIT (arm wrongly selected) vs 107 on the interpreter. Needs an equality test
   against the extracted slot, with the slot's boxed/ANY representation handled
   (int vs string vs float paths all differ).
2. **Tuple / struct / array sub-patterns in payload position** — still return
   `Bool(true)` (`control.rs`, the `Pattern::Tuple(_) | Pattern::Array(_) |
   Pattern::Struct { .. }` arm).
3. **Nesting deeper than one level** — measured, not assumed. For
   `case C(L2.S(L3.X(n)), tag)` over a three-level enum, the JIT returns 3 for
   BOTH an `L3.X` and an `L3.Y` subject (interpreter: 10 and 510). So the
   innermost level is neither tested (first arm always selected) nor bound
   (`n` reads 0, leaving just `tag`). `nested_payload_condition` deliberately
   descends one level only; making it fully recursive requires threading the
   extracted slot expression through as the new subject for both the condition
   and the binding walk.
4. **`codegen/instr/pattern.rs:96`** has an independent catch-all
   (`_ => iconst(1)`, "always match for now") on the MIR->Cranelift path, and
   `MirPattern::Variant { .. }` there also discards its `payload`. The HIR fix
   covers the lane exercised by `SIMPLE_EXECUTION_MODE=jit`; that MIR-level
   site should be brought to parity before anything relies on it.

## S4 (native payload arms)

Still gated. `is_native_payload_free_enum_match` (`compilability.rs:240`)
rejects any arm where `payload.as_ref().is_some_and(|p| !p.is_empty())`.
Accepting payload arms additionally requires the bare-identifier defect
(`case_bare_ident_is_irrefutable_binding_2026-08-01.md`) to be resolved and
items 1-4 above to be closed, since native would otherwise inherit them.
