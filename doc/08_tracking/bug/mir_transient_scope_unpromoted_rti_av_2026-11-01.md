# MIR transient scope frees unpromoted `rti` rows: E-MIR-TYPE-Transport / E-RTI-003 / access violation (2026-11-01)

## Symptom
A stage2 built from `release/1.0.0` at or after `33bba69184f` (#5709, "compiler:
bound MIR setup transient scopes") fails `native-build --entry-closure` on an
entry that pulls `lib.nogc_async_mut.fiber.io_reactor` / `lib.nogc_sync_mut.io.time_ops`
/ `compiler.frontend.*` (lane repro `test/p3_e0_repro/repro_io.spl`):

- `E-MIR-TYPE-Transport: invalid HirType kind carrier observed at MIR boundary
  owner=sleep_ms context=body ... caller_disc=-2 relation=already-invalid-at-caller`
  (also owners `fiber_io_close`, `frontend_parse_or_restore`,
  `parser_variant_named_dependencies`, `frontend_spab_load_v1`)
- `E-RTI-003: unsubstituted generic parameter in 'n:lib.nogc_async_mut.async.poll:...[p0]'
  reached a concrete consumer` (5x in `lib.nogc_async_mut.async.future`)
- `ICE[mir_lower] module compiler.frontend.core.parser: worker died inside this
  module (worker exit status -1073741819)` = 0xC0000005 access violation.

A stage2 built from the same sources minus #5709 (`2c7305bbbbb`, E0 branch on
`7c7444b8682`) lowers all 282 closure modules through MIR (`phase=mir done=282
succeeded=282 failed=0`). The pinned phase-3 stage2 (`ef0681fc0e1`) also lacks
#5709 and does not show the failure.

## Root cause
`MirLowering.rti: ReturnTypeInterfaceTable` was added by RTI PR1
(`d0e58600707`, 2026-10-27) two days after `promote_transient_owner`
(`src/compiler/50.mir/_MirLowering/transient_owner.spl`, last reconciled
`ed2581b83d3`, 2026-10-25) enumerated every `MirLowering` field as a
promotion root. Three more fields were likewise never added:
`rti_last_error`, `runtime_value_extern_abis`, and E0's
`erased_callback_record_bindings` (#5732).

#5709 (`src/compiler/80.driver/driver_pipeline_lowering.spl`) wraps
`prescan_module_struct_names` in `transient_array_scope_begin_v1()` /
`_driver_mir_inventory_scope_end`. That prescan calls
`prescan_module_functions_v1`, which registers `ReturnTypeRow`s into
`self.rti.register_rows(...)` (`module_lowering.spl:1954`). The rows are
allocated inside the scope; `promote_transient_owner` never retags `self.rti`,
so `transient_array_scope_end_v1()` frees them. Every later consumer reads the
dangling rows: when the freed memory still looks like an enum the
`_sffi_hir_type_discriminant` probe reports an invalid carrier
(E-MIR-TYPE-Transport, E-RTI-003); when it has been reused, the read is an
access violation. It is a use-after-free, not a type error, which is why it
surfaces as an AV instead of a diagnostic.

E0 (#5732) is not the cause: the E0-branch compiler without #5709 passes, and
the failing owners (`sleep_ms`, `fiber_io_close`) contain no generics.

## Fix
`promote_transient_owner` promotes `rti`, `rti_last_error`,
`runtime_value_extern_abis`, `erased_callback_record_bindings`.
Regression gate: `test/01_unit/compiler/mir/transient_owner_promotes_every_field_spec.spl`
asserts every `struct MirLowering` field is a `promote_and_release_transient_owner_roots`
root, so a new field can no longer be silently freed by a scope.

## Phase 3
Run 13 may rebase onto #5732 (E0); it must include this fix (or exclude #5709)
or MIR lowering dies on the first scoped prescan.
