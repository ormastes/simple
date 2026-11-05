# match_unqualified_imported_enum_variant_default_arms

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: B5b: match has multiple wildcard/binding default arms (binding Clocked in VhdlBackend.compile_process); variants of re-exported VhdlProcessKind are treated as bindings.

Workaround (tagged `@workaround bug=match_unqualified_imported_enum_variant_default_arms_2026-10-24`): qualify case patterns VhdlProcessKind.X (src/plugins/backend_vhdl/vhdl_backend.spl). Also vhdl_design_catalog.spl: Ret(nil) -> Ret(None) (nil into optional payload outside unsafe is a real source error).

Root fix location: src/compiler/50.mir/_MirLowering/module_lowering.spl and _MirLoweringExpr/expr_dispatch.spl: resolve bare variant patterns through re-exported (export use) enums.

### 2026-11-05 frontend-match lane
Compiler-side fix present (register_module_enum_inventory_v1; lexical import variant registration; module_enum_inventory_spec 5/5). Remaining: seed Rust interpreter does not match a bare payload-variant arm (`case Clocked:`), so match_bare_payload_variant_arms_spec fails on bin/simple.exe with "missing return in non-unit function"; JIT with a main is correct. Workaround revert needs stage3.

## 2026-11-05 — FIXED (mirp2 family A)
Root fix landed in 02e4b499e4a (expr_dispatch.spl bare payload-variant arm upgrade). Native evidence: s3_fable44.exe (2026-11-05 15:15 build), s3sanity run_case `mirp2a_enum` (enum ==/!= on payload-free enums, list membership by ==, payload-variant match, bare payload-variant arms) -> `CHECKS=10`, rc=0. Durable spec: test/01_unit/compiler/50.mir/enum_eq_and_match_lowering_spec.spl (interpreter 3/3).
The VHDL call site keeps the qualified `VhdlProcessKind.X(_)` form as ordinary code; its @workaround tag is removed.
Residual (not MIR, seed interpreter / family E): `bin/simple.exe run test/01_unit/compiler/match_bare_payload_variant_arms_spec.spl` still fails with "missing return in non-unit function 'name_of'" — the Rust seed treats bare payload-variant arms as bindings.
