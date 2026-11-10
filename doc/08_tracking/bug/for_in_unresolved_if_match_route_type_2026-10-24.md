# for_in_unresolved_if_match_route_type

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: for-in over non-array iterables unsupported (#143), collection mir type I64 (driver_source_pipeline_loading.spl:568,577,654): 'val route = if..: match..Ok(v): v else: call()' initializer type unresolved, so route.* fields are I64.

Workaround (tagged `@workaround bug=for_in_unresolved_if_match_route_type_2026-10-24`): annotate 'val route: PackageIndexRouteV1' and import the type (src/compiler/80.driver/driver_source_pipeline_loading.spl).

Root fix location: src/compiler/50.mir/mir_lowering_stmts.spl (#143 site) and if-expression type unification where an arm is a match with early-return Err arms.

### 2026-11-04 triage (c28-w1b) — not reproducible on the interpreter, stays open
Same spec file as above (if/match cases, with and without the early-return Err arm, then `for x in route.items`):
no fatal MIR error, 2/2 pass. Side observation: the same fixture emits a NON-fatal "non-exhaustive enum match on
'RouteLoad' ... Arms are textually exhaustive" diagnostic when the `match` is the tail of an `if` arm, i.e. the
exhaustive-arms check misfires in that position (arms Loaded + Failed cover the enum). Worth a separate row.
The real trigger is the cross-module `PackageIndexRouteV1` type from `driver_source_pipeline_loading.spl`; verify on stage3
by removing the `val route: PackageIndexRouteV1` annotation. Workaround kept.

### 2026-11-10 fix (fable p2 lane) — fix-implemented-verification-pending
Reproduced on the pure-Simple MIR lowering path with a TWO-module fixture (the
cross-module trigger named above): `val route = if c: <match pick(): Ok(v): v /
Err: return> else: make()` with Route/pick/make from `lib.dep` gives
`#143 (collection mir type: Unit)`. Root cause is in
`mir_merged_arm_struct_name` (`mir_lowering_stmts.spl`): the Ok-payload arm
records the BARE struct name (`Route`, name-keyed ret-shape registry), the
call/constructor arm records the qualified `lib.dep::Route`; the textual
mismatch dropped the merge slot's struct identity, so `route.items` lowered to
Unit. Fix: `mir_merged_struct_name_pair` unifies exactly one bare spelling with
its qualified one (qualified kept; two differing qualified names still
disagree). Specs: `test/01_unit/compiler/50.mir/for_in_if_match_cross_module_route_spec.spl`
(4/8 red -> 8/8 green) and `test/01_unit/compiler/50.mir/if_merge_arm_struct_name_spec.spl`
(8/8). The `val route: PackageIndexRouteV1` workaround annotation stays until
a stage-3 native build verifies; remove it then.
