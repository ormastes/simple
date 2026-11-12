# Seed: a bare unit variant in a struct-field sub-pattern is neither tested nor bound

**Status:** OPEN (filed 2026-11-12, aarch64 Linux; flagged by the Fable review of PR #8516)
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
