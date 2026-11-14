# MIR accepts `nil` into a non-optional scalar enum payload slot

Bug ID: `enum_payload_nil_into_scalar_slot_accepted_2026-11-14`
Severity: P2. Status: open. Layer: `50.mir` (`enum_constructor_payload.spl`,
`enum_payload_local_compatible`).

## Symptom

```simple
enum E:
    N(n: i64)
fn mk() -> E:
    E.N(nil)
```

lowers with no MIR error in safe code. `enum_payload_local_compatible` special-cases
`NilLit` only for `Optional`, `Nil` and nominal (`Named`) slots; for `Int` / `Float` /
`Bool` it falls through to the MIR-carrier check, and nil's carrier is I64, so an `i64`
slot admits it. The owner rule is that `nil` is unsafe-only and never fills a
non-optional slot.

Found while reviewing `work/stage3-mir-let-payload-20261114` (seed
`simple-covexpr-20261114/build/seed-base/simple`, release `6a71372cabc`): a probe case
`E.N(nil)` expecting `payload type mismatch at 0` failed. That branch closes the same hole
for dict literal entries only (`enum_payload_dict_entry_nil_vetoed`), because its dict
change made that path newly reachable; the top-level case predates it.

## Why not fixed with it

It changes what top-level payloads are accepted, which was outside that branch's review
scope, and has not had a census of literal `nil` arguments into scalar payload slots across
the tree, nor a Stage 3 run. (The 12 `hir_codec.spl` scalar joins noted in
`stage3_let_payload_unguarded_optional_arm_2026-11-14.md` pass a variable, not a `NilLit`, so
a literal-only veto would not touch them; a variable whose value is nil is a separate gap.)

## Fix

Refuse `NilLit` in `enum_payload_local_compatible` for every non-optional, non-`Nil` slot
outside `unsafe:`, after migrating the scalar sites to `None` / an optional slot.
