# module_surface_projected_type_shape undefined — every --hir-shard child dies E1002 (2026-08-22)

**Status:** FIXED (this commit). **Severity:** blocker for stage1 sharded native build.

## Symptom
run11b (tree `a6233953eca`, seed `e5f12c93`): every `--hir-shard` worker child
(`src/app/cli/native_build_worker.spl`) died at `[build] surface_build 5/687` with
`error[E1002]: function module_surface_projected_type_shape not found` (printed twice),
then `[hir-shard] 0/8 shard(s) completed`.

## Root cause
Commit `50feb3ba227` ("fix(hir): freeze composite import projections") landed the
CALL SITES of two helpers in
`src/compiler/20.hir/hir_lowering/module_surface_declarations.spl` (composite-index
loop, `module_surface_projected_type_shape(field.type_)` and
`module_surface_projected_type_name(field.type_, shape)`) and the new
`ModuleSurfaceCompositeIndex.field_shapes` / `field_type_names` columns — but their
DEFINITIONS were never committed anywhere in the tree (`git log -S` finds only the
callers). Not an export/`use` problem: the symbol did not exist.

Why the driver looked fine: the seed driver interprets lazily and only reports an
unresolved call when the body executes; the shard worker lowers the module as a whole
for native, so the missing function is a hard E1002 at `surface_build`. The same
E1002 reproduces on the interpreter as soon as the helper is imported by name (spec).

## Fix
Define both helpers in the same file, mirroring the existing scalar pair on
`ModuleSurfaceField` (`type_name` / `array_element_name`):
`shape` ∈ {`named`, `array`, `other`}; `name` = named type / array element / `""`.

## Reproduce
`test/01_unit/compiler/hir/module_surface_projected_type_shape_spec.spl` — pre-fix:
`Results: 4 total, 1 passed, 3 failed` (`semantic: function
module_surface_projected_type_shape not found`); post-fix: 4/4 pass. Neighbor
`module_surface_callable_from_function` import kept as the control.

## Lesson
A landing that adds callers must carry their definitions in the same commit; this is
the third "missing half" landing this week (cf. `origin_main_unbuildable_missing_half_1e40de916bb_2026-08-18.md`).
