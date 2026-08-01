# Nested enum payload sub-patterns always-match and never-bind on the JIT

**Date:** 2026-08-01
**Status:** Fixed for variant sub-patterns at ANY depth, literal sub-patterns,
range/or sub-patterns, and literals inside struct sub-patterns. Tuple and array
sub-patterns remain open — see the residue section, which now records a
DIFFERENT and larger root cause than "irrefutable".
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

## Residue round 2 — dispositioned 2026-08-01 (second pass)

Items 1 and 3 of the original residue list, plus a sibling of item 2, are now
**fixed**. `nested_payload_condition` was made recursive over an *expression*
slot rather than a local index, so the extracted slot of one level becomes the
subject of the next; `subpattern_condition` (new) dispatches per sub-pattern
kind, and `bind_nested_payload` (new, `stmt_lowering.rs`) is the matching
recursive binding walk. Both must agree on slot extraction — a mismatch
selects an arm on one slot and binds from another — so the extraction is
factored into `payload_slot_expr`.

Fixture: `test/fixtures/compiler/nested_payload_subpattern_depth_matrix.spl`.
Measured JIT `BADCOUNT 8 -> 0`, interpreter `BADCOUNT 0` before and after
(true-positive control: the interpreter recurses correctly, so it pins that the
expected values themselves are right). Both fixtures carry a live sentinel row
that proves `check` can still report a mismatch.

| Sub-pattern kind / depth | before (JIT) | after (JIT) | interpreter |
|---|---|---|---|
| variant, depth 2 | correct since `1957ea41f64` | correct | correct |
| variant, depth 3 (`C(L2.S(L3.Y(m)), tag)`) | 703 (inner not bound) | 710 | 710 |
| variant, depth 4 (`C(L2.S(L3.X(L4.P(a))), tag)`) | 3 for BOTH `P` and `Q` | 10 / 510 | 10 / 510 |
| integer literal, multi-slot (`A(0, y)`) | 7 (arm wrongly selected) | 116 | 116 |
| integer literal, single-slot (`B(5)`) | 55 | 209 | 209 |
| text literal (`Tag("hi")`) | 1 | 2 | 2 |
| literal inside struct sub-pattern (`Wrap(Point(0, b))`) | 4 | 107 | 107 |
| range / or sub-pattern | irrefutable | tested | correct |
| **tuple sub-pattern** (`V((0, b))`) | 0 | **0 — still open** | correct |
| **array sub-pattern** (`V([a, b])`) | 0 | **0 — still open** | correct |

Which implementation this reaches was proved by instrumentation, not by
reading: `SIMPLE_DEBUG_PATTERN_LOWER=1` (default off) makes
`subpattern_condition` announce itself. It fires **11 times under
`SIMPLE_EXECUTION_MODE=jit` and 0 times under
`SIMPLE_EXECUTION_MODE=interpreter`** for the depth-3 probe. That is the direct
evidence for the standing warning that the interpreter uses
`interpreter_patterns.rs` and never this HIR walk — and note that match ARMS
route through the statement-form twin `lower_pattern_condition_stmt`, not the
expression form, which is why an unconditional print in
`lower_pattern_condition`'s own `Pattern::Enum` arm emits nothing for a program
that trips this path.

### Still open

1. **Tuple and array sub-patterns — the root cause is NOT irrefutability.**
   Measured on the JIT, base and fixed alike: `match xs: case [a, b]: a + b`
   over `[1, 2]` returns **0**, and `case (a, b)` over `(1, 2)` returns **0** —
   at *top level*, with no enum involved at all. The binders are never emitted;
   array/tuple destructuring has no binding lowering on this path. Adding the
   length/arity test alone would move `[1,2,3]` from the `[a,b]` arm to the
   `[a,b,c]` arm and still answer 0 + 100 = 100 instead of 106 — a *different*
   wrong answer, not a fix. So the condition side deliberately still returns
   `None` for `Pattern::Tuple` / `Pattern::Array`, and the binding gap must be
   closed first. Fixture rows exist in the probe set but are intentionally NOT
   added to the in-tree matrix, which must stay green.
2. **`codegen/instr/pattern.rs:96`** — unchanged, still an independent catch-all
   (`_ => iconst(1)`, "always match for now") on the MIR->Cranelift path with
   `MirPattern::Variant { .. }` discarding its `payload`. Owned by a separate
   lane. The HIR fix covers the lane exercised by `SIMPLE_EXECUTION_MODE=jit`;
   that MIR-level site should be brought to parity before anything relies on it.

## S4 (native payload arms)

**Still gated, and this change does not ungate it.**
`is_native_payload_free_enum_match` (`compilability.rs:240`) is untouched and
still rejects any arm where `payload.as_ref().is_some_and(|p| !p.is_empty())`,
so `compile --native` continues to fail closed with `[PatternMatch]`. Three
blockers remain, all of which native would otherwise inherit:

* tuple/array destructuring emits no bindings (open item 1 above);
* the MIR->Cranelift catch-all still matches everything (open item 2 above);
* the bare-identifier defect
  (`case_bare_ident_is_irrefutable_binding_2026-08-01.md`).

Do not flip the gate on the strength of the depth/literal rows alone.
