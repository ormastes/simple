# MIR optional module-global / nested optional nil specs red on seed (stale specs, not product)

- **Status:** fixed (spec-only), 2026-11-04
- **Specs:** `test/01_unit/compiler/50.mir/{module_global_optional_none_static,stage2_module_global_optional_assign_binding,nested_optional_text_nil_pattern}_spec.spl`

## Causes
1. Two global specs call `lower_bootstrap_closure_module` on a fresh `MirLowering` without the
   enum inventory the driver registers first (`driver_pipeline_lowering.spl`
   bootstrap_fixed lane -> `register_module_enum_bootstrap_inventory_v1`). Lowering
   `Some(..)` then fails `enum construction: missing runtime identity for 'Option'`. The product
   fix (Optional arm in `runtime_module_initializer_type_fallback`, module_lowering.spl) was
   already correct. Specs now register the inventory like the driver.
2. `nested_optional_text_nil_pattern_spec` asserted an empty error list but the warn-only
   `non-exhaustive enum match on '..'` note (switch_operators_calls.spl, BUG-2026-08-01) is
   emitted for every no-default match; other 50.mir specs filter it. Filter added for that message
   only. The HIR owner-rejection text became `qualified enum pattern owner differs from subject
   owner` (f1b5fe09df4); expectation updated, rejection still asserted.
