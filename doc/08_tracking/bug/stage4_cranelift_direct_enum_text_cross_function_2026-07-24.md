# Bug: stage4 cranelift-direct — cross-function enum TEXT payload mis-decodes to a pointer

- **Date:** 2026-07-24
- **Lane:** stage4 self-hosted AOT (`native-build --backend cranelift`, cranelift-direct)
- **Severity:** correctness (wrong runtime output; compiles + exits 0)
- **Status:** OPEN — root-caused, blocked on a deeper codegen defect (see below)

## Symptom

A multi-field enum whose payload includes a `text` field, when **matched in a
different function than the one that constructs it**, prints the raw i64 tuple
word (a heap pointer) instead of the string.

```simple
enum K:
    A(text, i64?, text)
    B(i64)

fn classify(k: K) -> text:
    match k:
        case K.A(e, n, v): "A e={e} v={v}"   # e, v come out as pointers
        case K.B(x):       "B x={x}"

fn main():
    print(classify(K.A("x", nil, "payload")))   # want: A e=x v=payload
                                                 # got:  A e=<ptr> v=<ptr>
```

Same-function matches decode correctly (fixed by 6e6beb43d51). Integer payloads
(`n`, `x`) always decode correctly; only `text` slots are affected.

## Mechanism (what works, what doesn't)

Multi-field enum payloads are boxed into an `rt_tuple` (`box_tuple_payload`).
`lower_enum_match` unboxes each slot with `rt_tuple_get`, which returns a raw
i64. To render a slot as a string it must be retagged via `rt_interp_cstr`.
Whether a slot is text is looked up in `self.enum_tuple_text_slots`
(`"{enum}::{variant}::{field_idx}"`).

- **Construction-site registration** (`box_tuple_payload`, keyed off
  `local_is_str` on the MIR type) is **reliable** but **order-dependent**: it
  only populates the side table when the constructing function is lowered
  *before* the matching function. Functions lower in definition order, so a
  callee that matches (`classify`) lowered before `main` sees an empty table.
  This is why cross-function fails while same-function works.

- **Declaration-driven registration** (the natural fix: register text slots from
  the enum decl during type registration, before any body lowers) is **blocked**
  by a codegen defect — see below.

## Root blocker: nested enum-typed HIR field mis-decodes in native codegen

Iterating `module.enums.values()` and reading a variant's declared field types:

```simple
val enum_def = enum_values[ei]            # HirEnum from module.enums.values()
val v = enum_def.variants[vi]
v.name          # TEXT field — decodes correctly
v.kind          # HirVariantKind ENUM field — MIS-DECODES
match v.kind:
    case HirVariantKind.Tuple(vtypes): ...   # NEVER taken for a real Tuple variant
    case _: ()                               # always falls here
```

Verified by instrumentation (build `bj3hf3tig`, 2026-07-24): for `enum K`,
`enum_def.variants.len()` == 2 and `v.name` are correct, but the
`HirVariantKind.Tuple` arm is never entered — the `.kind` enum field's
discriminant/payload reads garbage. `lower_variant`
(`declaration_lowering.spl`) provably builds `HirVariantKind.Tuple(hir_types)`,
so the HIR is correct; the defect is on **read** in the native-compiled
`module_lowering`. This is the same class as the known `Dict.values()[i]`
struct mis-decode, extended to a **nested enum-typed field** — and it blocks
every declaration-based approach to text-slot detection.

## Fixes already landed (this cures the same-function case)

- `77d41f2c1a5` — bind enum-match payloads into the `find_local` store
  (compile-regression from `033d79338a1`; enum matches failed to compile with
  "undefined variable").
- `6e6beb43d51` — initialize `enum_tuple_text_slots: {}` in the `MirLowering`
  ctor (it was NIL-FILLED, so all construction-site writes were lost; this fixes
  **same-function** multi-field enum text: `v=payload`).

## Next steps (candidate approaches, all non-trivial)

1. Fix the underlying nested-enum-field mis-decode so `v.kind` reads correctly
   (deepest, highest-leverage — unblocks decl-driven registration cleanly).
2. Order-independent construction pre-pass: walk all function bodies for enum
   construction exprs and register text slots (via arg MIR types, which decode)
   before lowering any body. Avoids reading `.kind` entirely.
3. Runtime slot-type tags in the boxed tuple so `lower_enum_match` can decide
   text-ness at runtime without the side table (representation change).
