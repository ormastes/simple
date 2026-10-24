# for-in #143 on `val x = if c: <match> else: call()` (if-merge first-arm I64 wins)

Symptom (Phase-3 build): `compiler.driver.driver_source_pipeline_loading: MIR lowering error: for-in over non-array iterables ... (collection mir type: I64)`.

Site: driver_source_pipeline_loading.spl `val route = if native_group_inputs.len() > 0: <block ending in match> else: package_index_route_admitted_current_with_mode_v1(...)`, then `for dirty in route.dirty_modules` (and sibling loops).

Root cause: `lower_if` (50.mir/mir_lowering_stmts.spl) types the merged result via `mir_merge_arm_types(first, second)`, which only ever refined array element types and otherwise returned the FIRST arm. The then-arm (match with Result-payload arms) lowers to bare I64, so the struct-typed else-arm (call result) was discarded; `route.*` fields became I64.

Fix: `mir_merge_arm_types` returns `second` when `first` is I64 and `second` is `Struct(_)`. Arrays/other kinds unchanged.

Workaround (sibling lane, f64949e6b99): annotate `val route: PackageIndexRouteV1`.

Spec: test/01_unit/compiler/50.mir/if_merge_unresolved_arm_struct_for_in_spec.spl (NOT executed; no runnable full-CLI compiler here; fix unverified by bootstrap).
