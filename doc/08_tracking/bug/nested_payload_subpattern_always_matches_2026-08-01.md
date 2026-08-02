# Nested enum payload sub-patterns always-match and never-bind on the JIT

**Date:** 2026-08-01
**Status:** Fixed for variant sub-patterns at ANY depth, literal sub-patterns,
range/or sub-patterns, literals inside struct sub-patterns, and — as of the
third pass below — tuple and array destructuring both at top level and in
payload position.
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
| **tuple sub-pattern** (`V((0, b))`) | 0 | 0 — fixed in round 3 below | correct |
| **array sub-pattern** (`V([a, b])`) | 0 | 0 — fixed in round 3 below | correct |

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

1. ~~Tuple and array sub-patterns~~ — **FIXED, see "Residue round 3" below.**
2. **`codegen/instr/pattern.rs:96`** — unchanged, still an independent catch-all
   (`_ => iconst(1)`, "always match for now") on the MIR->Cranelift path with
   `MirPattern::Variant { .. }` discarding its `payload`. Owned by a separate
   lane. The HIR fix covers the lane exercised by `SIMPLE_EXECUTION_MODE=jit`;
   that MIR-level site should be brought to parity before anything relies on it.

## Residue round 3 — array/tuple destructuring, fixed 2026-08-01 (third pass)

The previous pass recorded this correctly: the root cause was **not**
irrefutability. Array and tuple patterns emitted **no binding statements
anywhere**. `collect_pattern_bindings` registered locals for `a`/`b` in
`case [a, b]:`, but nothing ever initialised them, so the arm was selected and
both names were read off the zeroed stack — `1 + 2` answered `0`, at top level,
with no enum involved.

Both halves were required, and the fix delivers both:

* **Binders.** `bind_subpattern` (`hir/lower/stmt_lowering.rs`) is now the single
  owner of sub-pattern binder construction — identifier, nested variant, tuple
  and array all route through it, and `bind_nested_payload` delegates to it
  rather than carrying its own duplicate match. `bind_sequence` walks array and
  tuple elements. Three call sites feed it: the top-level arm pattern, the enum
  payload loop, and the recursive nested-payload walk.
* **Length discriminator, arrays only.** `sequence_condition`
  (`hir/lower/expr/control.rs`) emits `rt_array_len(slot) == N`, or `>= N-1`
  when a `Pattern::Rest` is present, mirroring `interpreter_patterns.rs`. It is
  **not** emitted for tuples: a tuple's arity is fixed by its type, and
  `rt_array_len` returns `-1` on a Tuple heap object (the `as_typed_ptr!` tag
  check fails), so an arity test there would make every tuple arm fail to match.
  Tuple patterns take their refutability from their elements only.

Condition and binder share `sequence_element_slots`, so an element can never be
tested at one index and bound from another — the same discipline
`payload_slot_expr` enforces for enum payload slots.

**The half-fix signature was observed live.** After the condition half landed
but before the enum-payload loop routed array/tuple sub-patterns to a binder,
`payload_arr3` answered exactly **100** — right arm selected, binders still
zero. That is the documented different-wrong-answer, and it is why `arr3` (106)
is the row that separates a real fix from a length test.

Fixture: `test/fixtures/compiler/nested_payload_subpattern_depth_matrix.spl`,
extended with 14 rows. Measured JIT **`BADCOUNT 14 -> 0`** over those rows
(30 rows total, `BADCOUNT 0`); interpreter `BADCOUNT 0` before and after as the
true-positive control. `[jit-fallback]` occurrences: 0.

| Row | before (JIT) | after (JIT) | interpreter |
|---|---|---|---|
| `arr2` — `case [a, b]` over `[1,2]` | 0 | 3 | 3 |
| **`arr3` — `[1,2,3]` to the `[a,b,c]` arm** | 0 | **106** | 106 |
| `arr_too_short` — `[9]` | 0 | -1 | -1 |
| `arr_too_long` — `[1,2,3,4]` | 0 | -1 | -1 |
| `tup2` — `case (a, b)` over `(4,5)` | 0 | 9 | 9 |
| `arr_lit_hit` / `arr_lit_miss` (`[0, b]`) | 0 / 0 | 7 / 107 | 7 / 107 |
| `arr_rest_one` / `_many` / `_empty` (`[a, ...]`) | 300 / 300 / 300 | 305 / 305 / -1 | 305 / 305 / -1 |
| `payload_arr2` / `payload_arr3` (`Items([a,b])`) | 0 / 0 | 3 / 106 | 3 / 106 |
| `payload_tup_hit` / `_miss` (`Pair((0,b))`) | 0 / 0 | 7 / 107 | 7 / 107 |

`arr2`'s correct answer is 3 — the nil sentinel — so it doubles as a second
value-3 control alongside `d4_value3_ctrl`, while `arr3` at 106 cannot be
satisfied by a silently-nil binder. The live sentinel row still fires.

Which site the change reaches was proved by the same default-off probe, not by
reading. `SIMPLE_DEBUG_PATTERN_LOWER=1` on a top-level-only array/tuple program:
**0 hits on the base binary, 7 on the fixed one** (2 + 3 + 2 elements) — the
top-level arms previously never entered this walk at all. On the full fixture
the descent shows as `kind=Identifier` 19 -> 38 and `kind=Literal` 4 -> 6, with
`kind=Array`/`kind=Tuple` unchanged at 2 each (they were always *entered* in
payload position; they just returned `None` instead of descending). Still 0 hits
under `SIMPLE_EXECUTION_MODE=interpreter` and 0 with the flag off.

### Known scope limits (not regressions)

* A **struct** sub-pattern nested inside an array or tuple element
  (`case [Point(x, y), b]:`) is still not bound. The struct spellings are served
  by the `class_struct_fields` / `struct_info` paths in
  `build_pattern_binding_stmts`; duplicating them inside `bind_subpattern` would
  emit the same `Let` twice. Separate shape, untouched here.
* A `Pattern::Rest` with trailing elements in a non-array sequence has no
  addressable form; `sequence_element_slots` returns `None` for it and the
  caller keeps its previous behaviour. The parser only ever produces
  `Pattern::Rest` inside an array pattern (`parser_patterns.rs`, `LBracket`
  arm), so this is unreachable today rather than a silent wrong answer.

## S4 (native payload arms)

**Still gated, and this change does not ungate it.**
`is_native_payload_free_enum_match` (`compilability.rs:240`) is untouched and
still rejects any arm where `payload.as_ref().is_some_and(|p| !p.is_empty())`,
so `compile --native` continues to fail closed with `[PatternMatch]`. Of the
three blockers, **blocker 1 is now closed** and two remain:

* ~~tuple/array destructuring emits no bindings~~ — **CLOSED** by residue round 3
  above (HIR lowering; measured on the JIT lane);
* the MIR->Cranelift catch-all still matches everything (open item 2 above) —
  `codegen/instr/pattern.rs:96`, owned by a separate lane;
* the bare-identifier defect
  (`case_bare_ident_is_irrefutable_binding_2026-08-01.md`).

Do not flip the gate on the strength of the depth/literal/sequence rows alone.
The native column for `match` on an enum is **unmeasurable**, not passing:
native has no `match`-on-enum lowering at all, so `compile --native` refuses
these programs rather than answering them. Closing blocker 1 removes one reason
the gate must stay shut; it does not by itself make native correct.
