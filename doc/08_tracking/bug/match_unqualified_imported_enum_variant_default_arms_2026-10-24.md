# match_unqualified_imported_enum_variant_default_arms

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: B5b: match has multiple wildcard/binding default arms (binding Clocked in VhdlBackend.compile_process); variants of re-exported VhdlProcessKind are treated as bindings.

Workaround (tagged `@workaround bug=match_unqualified_imported_enum_variant_default_arms_2026-10-24`): qualify case patterns VhdlProcessKind.X (src/plugins/backend_vhdl/vhdl_backend.spl). Also vhdl_design_catalog.spl: Ret(nil) -> Ret(None) (nil into optional payload outside unsafe is a real source error).

Root fix location: src/compiler/50.mir/_MirLowering/module_lowering.spl and _MirLoweringExpr/expr_dispatch.spl: resolve bare variant patterns through re-exported (export use) enums.
