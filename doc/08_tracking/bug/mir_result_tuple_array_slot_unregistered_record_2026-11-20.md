# MIR: Result tuple `?` rejects `[Record]` slot of a provider record reached only via a callable

- **Status:** verification-pending
- **Date:** 2026-11-20
- **Area:** 50.mir — `_MirLowering/provider_metadata.spl`, `_MirLoweringExpr/result_tuple_payload.spl`
- **Found by:** x86_64-linux native build of the test runner (Stage 2 @ 1eb06660cb3)

## Symptom

```
MIR lowering error: unsupported Result tuple payload element type: slot 2 is Array
module=lib.common.traceability.case_events
```

`case_events.spl` runs `val parsed = parse_with_spans_and_issues(source)?`. The
payload is `(SdnValue, Dict<text, SdnSpan>, [SdnIssue])`, and the module
imports only the function, never `SdnIssue`.

## Root cause

`result_try_tuple_nominal_owner(record=true)` admits a `[Struct]` slot only when
four things are registered in the current `MirLowering`:

- the record's layout digest (`composite_layout_digests`, unique owner count),
- its field-type snapshot (`result_err_layout_types`),
- its field order,
- its field HIR types.

Only the module prescans (`prescan_module_struct_names` and the declaration
prescan) record the first two. The provider relocation path,
`register_provider_struct`, which also backs demand-on-read layout registration,
recorded field rows but no digest or snapshot. A provider struct that the
consumer reaches only through an imported callable's signature therefore had
field rows but no proof, and the tuple slot failed closed.

## Fix

- `register_provider_struct` now also calls `register_result_err_layout_types`
  and `register_composite_layout_identity`, mirroring the prescan, but only to
  fill a gap. If a prescan already recorded the identity, the relocated copy is
  skipped and never clears it.
  An ambiguous or conflicting identity still fails closed.
- `result_try_tuple_nominal_owner` calls `provider_layout_demand_v1` on the
  record name before it reads any layout table, the same way
  `resolve_field_index` does.

A record that has no provider layout at all is still rejected. No owner-less
admission was added, because element field reads would otherwise fall back to
GetField index 0.

## Evidence

- Spec: `test/01_unit/compiler/mir/result_tuple_array_slot_unimported_struct_spec.spl`,
  run seed-interpreted.
  - Before: 1/3 pass. The `?` lowering and the field-read cases fail with the
    exact error.
  - After: 3/3 pass. `issue.line` lowers to GetField index 1, and the case with
    no provider still fails closed.
- `result_try_provider_tuple_spec.spl` passes 10/10 after the change.
- Native fixture: `test/fixtures/compiler/result_tuple_array_slot_unimported/main.spl`.
  Stage 2 `native-build` reproduces the error. Verifying the fix natively needs
  a rebuilt stage compiler, which is why the status is verification-pending.

## Follow-up 2026-11-21: class slot (native verification failed)

Stage 2 built from b58524e5c2a (contains #10595, sha 1d2b0cf3) still fails the
native fixture, now with `slot 1 is Dict` (`Dict<text, SdnSpan>`). `SdnSpan` is a
**class**. `register_provider_class` relocated field rows and a snapshot but,
like the struct path before #10595, never recorded the layout digest, so a class
reached only through an imported callable failed `result_try_tuple_nominal_owner`.
The rejection diagnostic re-walks every slot, so after the first pass demanded
`SdnSpan` the reported slot moved from 2 to 1.

Fix: the same digest gap-fill in `register_provider_class`.

- Spec: new case "keeps a Dict class slot admitted after its layout is demanded",
  run seed-interpreted. Before the fix 4/5 pass; after, 5/5.
- The status stays verification-pending until a Stage 2 rebuilt from this fix
  passes the native fixture.
