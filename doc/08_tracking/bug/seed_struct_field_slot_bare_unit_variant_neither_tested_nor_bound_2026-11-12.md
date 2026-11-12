# Seed: a bare unit variant in a struct-field sub-pattern is neither tested nor bound

**Status:** FIXED in the seed (2026-11-12, work/bug-seedstructslot-20261112) — filed 2026-11-12, aarch64 Linux; flagged by the Fable review of PR #8516
**Severity:** P2 — silent wrong arm selection in seed-compiled code (native and `run` JIT)
**Area:** Rust seed HIR lowering, `src/compiler_rust/compiler/src/hir/lower/expr/control.rs` (line numbers below are at PR #8516 head `ef3471b953a`)
**Related:** `seed_tuple_pattern_bare_fieldless_variant_binds_hir_types_equal_true_2026-11-12.md` (PRs #8497, #8516)

## Defect

PRs #8497/#8516 give tuple elements, array elements and enum payload slots
their declared type, so a bare unit-variant name there is a variant test.
Struct-field slots were left out, and the two halves now disagree there:

- **Condition:** `struct_fields_condition` (control.rs:1572) tests each field
  through `subpattern_condition(&field_expr, field_pattern, ctx)` (:1599), which
  is `subpattern_condition_typed(.., TypeId::ANY, ..)` (:1134). With an ANY slot
  type, `subject_enum_has_unit_variant` is false, so the bare name is irrefutable.
- **Binding:** `collect_pattern_bindings` resolves the REAL field type for both
  spellings (named `Pattern::Struct` via `struct_field_list`, ~:2080-2090; and
  the positional class spelling through the `struct_field_list` fallback in the
  `Pattern::Enum` arm) and, with `in_slot = true`, drops the name from the
  arm's bindings because it is a unit variant of that field's enum.

Result: `Red` in a struct-field slot is neither tested nor bound, so the arm
matches every value.

## Repro (seed built from PR #8516 head `ef3471b953a`, native, cranelift)

```simple
enum Color:
    Red
    Green

class Holder:
    c: Color
    n: i64

fn named(h: Holder) -> i64:
    match h:
        case Holder { c: Red, n: n }: 1
        case _: 0

fn positional(h: Holder) -> i64:
    match h:
        case Holder(Red, n): 1
        case _: 0
```

| call | seed (#8516) | want |
|---|---|---|
| `named(Holder(c: Color.Green, n: 1))` | **1** | 0 |
| `named(Holder(c: Color.Red, n: 1))` | 1 | 1 |
| `positional(Holder(c: Color.Green, n: 1))` | **1** | 0 |
| `positional(Holder(c: Color.Red, n: 1))` | 1 | 1 |

## Fix direction (not applied)

Pass each field's declared type into the condition walk:
`struct_fields_condition` should call `subpattern_condition_typed(&field_expr,
field_ty, field_pattern, ctx)` with the type `collect_pattern_bindings` already
looks up (`struct_field_list`), so the condition and binder agree, as they do
for tuple/array/payload slots. Pin it with a native fixture covering both the
named and positional spellings, plus a lowercase field binder as the negative.

## Fix (2026-11-12)

`struct_fields_condition` now calls `subpattern_condition_typed(&field_expr,
field_ty, field_pattern, ctx)` with the field's declared type (the same
`HirType::Struct` field list the binder reads), so the unit-only slot rule
(`subject_enum_has_unit_variant`) applies to struct fields too.

| probe (aarch64, native) | seed before (`eb3f4463c9d9`) | seed after (`7c8465195898`) | run-14 Stage 2 | seed tree-walk interp |
|---|---|---|---|---|
| `named(Holder(c: Green, ..))` | 101 (wrong) | 0 | — (named struct patterns: `unresolved name: n` in HIR) | 0 |
| `positional(Holder(c: Green, ..))` | 101 (wrong) | 0 | **101 (wrong)** | 0 |
| Red rows, lowercase field binder, payload-name field binder (5 rows) | correct | correct | correct | correct |
| `test/fixtures/compiler/struct_field_pattern_bare_unit_variant_native.spl` | exit 1 | exit 0 | — | — |

Scan of `src/` (single-line `case` / `if|elif|while val` patterns whose head
names a `class`/`struct`): **0** sub-patterns with a bare capitalized name, so
no seed-compiled Stage 2 behaviour changes. The scanner was checked against
the fixture (finds all three sites) and finds the 21 bare-name ENUM payload
sites (`BinOp(_, Eq, ..)` etc.), none of which head-names a struct/class.

Still open (pure-Simple, not this fix): run-14 Stage 2 gets the positional row
wrong the same way (`case Holder(Red, n)` matches a Green holder), and it does
not lower named struct patterns that bind a field (`unresolved name: n`).
