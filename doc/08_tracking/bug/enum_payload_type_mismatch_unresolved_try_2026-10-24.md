# enum_payload_type_mismatch_unresolved_try

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum construction 'BackendResult.Value': payload type mismatch at 0 (compiler.backend.interpreter process_module); payload from 'val r = call()?' is not typed as Value.

Workaround (tagged `@workaround bug=enum_payload_type_mismatch_unresolved_try_2026-10-24`): typed local 'val result: Value' (src/compiler/70.backend/backend/interpreter.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl (payload type check) plus the type inference of the ? operator in expression lowering: infer Ok payload type of the operand's Result<T,E>.
