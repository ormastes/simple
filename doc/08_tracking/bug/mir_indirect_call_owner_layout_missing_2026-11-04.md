# MIR: "indirect call return record has no declared owner layout" for imported provider structs

Status: fixed 2026-11-04 (branch work/mir-owner-layout-20261104)

## Symptom
`test/01_unit/compiler/50.mir/imported_struct_operator_owner_spec.spl`: 16/16 failed with
`indirect call return record has no declared owner layout`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `remember_function_value_return`).
Only this spec in the triage logs carries that message; the other cluster files have different causes.

## Root cause
`remember_function_value_return` folds the declaration's `composite_layout_key`
(`lib.first::SharedRecord`) through `declared_struct_layout_key`, which relies on
`struct_identity_layout_key`. The provider struct registration in
`src/compiler/50.mir/_MirLowering/provider_metadata.spl` (struct branch, ~line 802)
registered the layout under `lib/first.spl::SharedRecord` (declaration spelling is a file path)
but never called `register_struct_identity_layout_key`, so the identity map was empty
(debug dump: `ids={}`, keys=`[lib.second::SharedRecord, lib/first.spl::SharedRecord]`) and
the dotted spelling could not fold onto the registered key. The local-struct sites
(module_lowering.spl:1922, :2771) and declaration_providers_v1.spl:473 already register it.

## Fix
One line: `self.register_struct_identity_layout_key(source, key)` after the provider
`register_composite_field_metadata(key, ...)`.

## Evidence
imported_struct_operator_owner_spec: 16 failed -> 16 passed. 14 other 50.mir specs unchanged (all pass).
