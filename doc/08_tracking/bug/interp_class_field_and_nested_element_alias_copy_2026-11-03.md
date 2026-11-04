# interp_class_field_and_nested_element_alias_copy_2026-11-03

Status: open (P1). See bug_db.sdn row of the same id.

## Update 2026-11-04

On a test-only seed built from origin/release/1.0.0,
`test/01_unit/compiler/interpreter/class_ref/class_ref_alias_shapes_indev_spec.spl`
passes 5/5 with `SIMPLE_INTERP_CLASS_REF=1` and fails 5/5 with
`SIMPLE_INTERP_CLASS_REF=0`.

The only remaining step is the staged default flip
(`interp_class_ref_default_flip_staged_2026-11-03`), which is gated on a
whole-tree test run with the flag on.
