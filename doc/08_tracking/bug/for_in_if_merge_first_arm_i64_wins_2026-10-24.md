# for-in #143 on `val x = if c: <match> else: call()` (if-merge first-arm I64 wins)

Symptom (Phase-3 build): `compiler.driver.driver_source_pipeline_loading: MIR lowering error: for-in over non-array iterables ... (collection mir type: I64)`.

Site: driver_source_pipeline_loading.spl `val route = if native_group_inputs.len() > 0: <block ending in match> else: package_index_route_admitted_current_with_mode_v1(...)`, then `for dirty in route.dirty_modules` (and sibling loops).

Root cause: `lower_if` (50.mir/mir_lowering_stmts.spl) types the merged result via `mir_merge_arm_types(first, second)`, which only ever refined array element types and otherwise returned the FIRST arm. The then-arm (match with Result-payload arms) lowers to bare I64, so the struct-typed else-arm (call result) was discarded; `route.*` fields became I64.

Fix: `mir_merge_arm_types` returns `second` when `first` is I64 and `second` is `Struct(_)`. Arrays/other kinds unchanged.

Workaround (sibling lane, f64949e6b99): annotate `val route: PackageIndexRouteV1`.

Spec: test/01_unit/compiler/50.mir/if_merge_unresolved_arm_struct_for_in_spec.spl (NOT executed; no runnable full-CLI compiler here; fix unverified by bootstrap).

## Verification — 2026-11-05

The source fix (mir_merge_arm_types keeps a Struct second arm over an
unresolved I64 first arm) was already landed when this pass ran; the bug doc's
"fix unverified by bootstrap" gap is now closed with executable evidence.

PR (merged into release/1.0.0): adds the direct contract spec
`test/01_unit/compiler/50.mir/if_merge_arm_types_spec.spl` — five scenarios
calling mir_merge_arm_types directly, including the pinned pre-existing array
element-refinement behavior (I64 element = "unknown", refined from a specific
second arm with size preserved). Discrimination confirmed: with the repair arm
removed, the key scenario fails (`expected i64 to equal struct`).

Evidence: seed interpreter on an aarch64 Linux host, 5/5 PASS; sibling
integration spec `if_merge_unresolved_arm_struct_for_in_spec.spl` 1/1
unchanged. Manual:
`doc/06_spec/01_unit/compiler/50.mir/if_merge_arm_types_spec.md`.
End-to-end stage-3 validation remains pending on an admitted self-hosted
binary; the sibling-lane `val route: PackageIndexRouteV1` workaround
annotation is intentionally left in place.
