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

## Update 2026-11-06

The staged default flip landed as `6c7b4db3d39` (merged 2026-11-04,
`7e3b0244cc3`). Re-verified on a seed from `f1390d48254`:
`class_ref_alias_shapes_indev_spec` 5/5 (0/5 with `SIMPLE_INTERP_CLASS_REF=0`),
`class_ref_alias_shapes_spec` 6/6, `class_element_reference_spec` 4/4 (2/4 off),
`dict_class_value_identity_spec` 5/5 (1/5 off),
`class_ref_interp_jit_consistency_spec` 11/11 (10/11 off).
Residual the flip exposed: three argument write-back shapes through class
chains (`f(x, x.items)` with `mut b: Box`, `f(o.h.items)` into a `mut`
param, `f(o.h.cfg)` non-mut struct) lost mutation with the flag ON —
`engine_divergence_mutation_class_spec` was 0/2 on, 2/2 off. Fixed in
commit "fix(interp): argument write-back through class reference chains" (ClassInstance arms in `set_nested_path` /
`merge_subject_step`, mut-class-param clobber guard); pinned by
`class_ref/class_ref_arg_writeback_spec.spl` (1/6 before, 6/6 after).
Coordinator owns the bug_db status change.
