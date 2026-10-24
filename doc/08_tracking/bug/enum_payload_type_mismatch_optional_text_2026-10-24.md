# enum_payload_type_mismatch_optional_text

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum construction 'CompileResult.CodegenError': payload type mismatch at 0 (driver_aot_codegen_outputs compile_to_c_directory); text? narrowed via 'if val' is not accepted as text.

Workaround (tagged `@workaround bug=enum_payload_type_mismatch_optional_text_2026-10-24`): annotate cmake_err: text? and coalesce with ?? to a typed text local (src/compiler/80.driver/driver_aot_codegen_outputs.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl: accept narrowed optional binding as its inner type.
