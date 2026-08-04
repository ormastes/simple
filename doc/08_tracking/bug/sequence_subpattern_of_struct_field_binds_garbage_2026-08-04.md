# Array/tuple sub-pattern of a STRUCT FIELD bound garbage on the JIT

**Status:** FIXED 2026-08-04.
**Found:** 2026-08-04, while fixing top-level struct-pattern refutability.
**Engines:** JIT only. The tree-walk interpreter answered every row correctly
throughout, so an interpreter-only run could never see this.

## Symptom

```
struct Holder:
    xs: [i64]
    t: (i64, i64)

fn f(h: Holder) -> i64:
    match h:
        case Holder([a, b], (c, d)):
            print("a={a} b={b} c={c} d={d}")
            a + b + c + d
        case _: -1
```

```
a=<value:0x6> b=1 c=2 d=5      # JIT, before
f 64                            # correct is 6 + 8 + 2 + 5 = 21
```

The TUPLE field bound correctly (`c=2 d=5`); the ARRAY field did not — `a` came
back as an undecoded tagged value whose payload was the right number, and `b`
was `1` instead of `8`.

## Root cause — the binding TYPE, not the addressing

The arm selection was always right (element literal test and array length
discriminator both worked over a struct-field slot), which correctly ruled out
the irrefutable-matcher family and `sequence_element_slots`. It also made the
addressing a red herring: an earlier attempt to materialise the field into a
compiler-generated temp local inside `bind_struct_fields` changed nothing,
because the receiver was never the problem.

The problem was one level up, in `collect_pattern_bindings`
(hir/lower/expr/control.rs). Its `Pattern::Enum` arm resolved payload field
types via `get_enum_variant_field_types_with_hint` — an **enum-only** lookup.
The parser cannot tell the positional class spelling `Holder([a, b], (c, d))`
from an enum variant, so it hands it over as `Pattern::Enum` with a STRUCT name
in `variant`. That lookup answered `None`, so every field sub-pattern was typed
`ANY`.

`ANY` then propagated one level further down: the `Pattern::Array` arm resolves
its ELEMENT type from `expected_ty`, and `ANY` is not an `HirType::Array`, so
`a` and `b` were registered as `ANY` locals too. `bind_sequence` emitted
`ANY`-typed `Let`s into `ANY`-typed locals, MIR picked generic boxing, and the
element surfaced as an undecoded tagged value. This is exactly the failure the
in-tree comment on that same `Pattern::Array` arm already warned about ("An
ANY-typed binding makes MIR pick generic boxing and can surface an i64 element
as a misformatted value at use sites") — the struct spelling simply never
reached it with a real type.

The `hoisted` control worked for the same reason it looked mysterious: a
top-level `case [a, b]` over `val ys = h.xs` enters `collect_pattern_bindings`
with `expected_ty = [i64]`, so the element type resolved and the locals were
`i64`.

## Fix

Two fallbacks in `collect_pattern_bindings`, both reusing `struct_field_list`,
the SAME resolver `bind_struct_fields` and `struct_fields_condition` already
use for the addressing half:

* `Pattern::Enum` — when the enum-variant lookup answers `None`, fall back to
  the struct field list for `variant`, in declaration order (positional
  spelling `Holder([a, b], (c, d))`).
* `Pattern::Struct` — was hardcoded `TypeId::ANY` for every field; now resolves
  each field's declared type BY NAME (named spelling `Holder { xs: [a, b] }`).

## Per-engine result

| row | interpreter | JIT before | JIT after |
|---|---|---|---|
| `d2_seq_hit`  | 14  | 56  | 14  |
| `d2_seq_miss` | 114 | 156 | 114 |
| `d2_seq_len1` | 13  | 56  | 13  |
| `d2_seq_len2` | 121 | 164 | 121 |

## Coverage

`test/fixtures/compiler/top_level_struct_subpattern_matrix.spl`, rows
`d2_seq_hit` / `d2_seq_miss` / `d2_seq_len1` / `d2_seq_len2`, moved out of
`OPENCOUNT` and into the `BADCOUNT` gate. `OPENCOUNT` is kept as a live,
always-printed tally so a regression of this family reappears as a non-zero
count rather than silently disappearing from the file.

An A/B of every fixture in `test/fixtures/compiler/` between the pre-fix and
post-fix binaries (md5-distinct) showed exactly two diffs: this fixture going
4 FAIL -> 4 PASS, and `native_option_uniform_tagged_abi_repro.spl` printing
different raw pointer addresses (ASLR, not a behaviour change).
