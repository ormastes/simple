# bare_result_return_type_any_payload

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: unsupported Result unwrap/unwrap_err payload type: payload is Any (linker_wrapper_helpers.spl:77): find_runtime_binary declared -> Result with no type arguments.

Workaround (tagged `@workaround bug=bare_result_return_type_any_payload_2026-10-24`): spell Result<text, text> (src/compiler/70.backend/linker/linker_wrapper_helpers.spl).

Root fix location: src/compiler/80.driver/driver_pipeline_lowering.spl (Result unwrap payload check) - either reject bare Result at type check or infer from returns.
