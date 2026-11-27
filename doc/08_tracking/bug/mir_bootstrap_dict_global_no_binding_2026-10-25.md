# MIR: ambient-bootstrap dict globals had no store target (2026-10-25)

**Symptom.** Stage3 whole-program MIR run (`build/s3-bis-new/build.log`): 113
unique `MIR lowering error: assignment target has no local binding` sites across
32 files (aspect_registry.spl 18, ast_coverage_inventory.spl 14, mir_data.spl 13,
rt_criticality_registry.spl 12, driver_source_loading.spl 3, ...). Every target
is a module-level dict global (`var D: Dict<K, V> = {}` / `{K: V} = {}`).

**Root cause.** `lower_static` (`50.mir/_MirLowering/module_lowering.spl`)
returns without a static for DictLit globals and hands ownership to
`lower_runtime_module_initializers_named`, the only producer of the static and
its `global_statics_by_id` mirror. The non-bootstrap path and the flat bootstrap
path call it; the ambient-bootstrap (`SIMPLE_BOOTSTRAP=1`) branch of
`lower_module` did not. `lower_assign_var` then missed `find_global_static`,
fell to `find_local`, and failed.

**Fix.** Call `lower_runtime_module_initializers(module, consts, 0)` in the
ambient-bootstrap branch after `bootstrap_mir_functions_reset()` and before any
function body. Genuinely unbound targets still fail closed.

**Regression.** `test/01_unit/compiler/50.mir/bootstrap_dict_global_assign_binding_spec.spl`.
Not executed locally: only the Rust seed exists on this host and it fails to
parse the current stdlib. Overlap: PRs #4537/#4543 touch enum payload typing /
qualified layouts, not global stores.
