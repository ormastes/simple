# Bug: nil Dict receiver — `.get()` returns phantom Some while `.len()` returns -1 (stub Module, stage-4 segfault lineage)

**Date:** 2026-07-27
**Status:** Open
**Area:** native codegen (Dict nil-receiver methods) + Rust seed (HirLowering field-type inference)

## Summary

During stage-4 bootstrap, `HirLowering.register_imported_symbol` operates on a
stub `Module` whose dict fields (e.g. `imported_const_decls`) were never
initialized. The seed nil-fills omitted struct-init fields, so the field holds
nil. Two root defects:

1. **Native codegen, phantom Some:** `.get(key)` on the nil Dict receiver
   returns a phantom non-nil Option (a "Some" wrapping garbage) while `.len()`
   on the same receiver returns -1. Downstream code trusts the phantom Some and
   dereferences garbage — the stage-4 bootstrap segfault lineage. The
   fail-closed contract is: `.get()` on a nil receiver must return nil, and
   `.len()`/`.get()` must agree (len() <= 0 implies get() -> nil).

2. **Seed field-type inference, hair-trigger control-flow sensitivity:** the
   seed's field-type inference in `HirLowering.register_imported_symbol` is
   sensitive to the guard's control-flow shape — four distinct guard shapes
   each broke with `cannot infer field type ... imported_const_decls`, making
   it impossible to guard the nil receiver at the call site without tripping
   inference.

## Repro spec

`test/01_unit/compiler/hir/nil_dict_receiver_phantom_option_spec.spl` — a
deliberately RED spec pinning the desired fail-closed contract (defect 1):

- `it "nil dict receiver returns nil from get, never a phantom value"` —
  `.get("k")` on a nil-filled Dict field must be nil.
- `it "len and get agree on a nil dict receiver: non-positive len implies nil
  get"` — if `.len() <= 0` then `.get()` must be nil.

The spec constructs a `StubModule` with an omitted (hence nil-filled)
`imported_const_decls: Dict<text, i64>` field, mirroring how the compiler hits
the receiver. It is EXPECTED RED under native codegen until the nil-receiver
fix lands; per repo convention for filed defects it stays visibly red (no
`skip()` — precedent: `rv32_trap_completeness_spec.spl`). Interpreter
semantics may differ from native; the spec's value is as the native-contract
pin.
