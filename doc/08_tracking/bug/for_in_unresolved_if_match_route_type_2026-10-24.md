# for_in_unresolved_if_match_route_type

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: for-in over non-array iterables unsupported (#143), collection mir type I64 (driver_source_pipeline_loading.spl:568,577,654): 'val route = if..: match..Ok(v): v else: call()' initializer type unresolved, so route.* fields are I64.

Workaround (tagged `@workaround bug=for_in_unresolved_if_match_route_type_2026-10-24`): annotate 'val route: PackageIndexRouteV1' and import the type (src/compiler/80.driver/driver_source_pipeline_loading.spl).

Root fix location: src/compiler/50.mir/mir_lowering_stmts.spl (#143 site) and if-expression type unification where an arm is a match with early-return Err arms.
