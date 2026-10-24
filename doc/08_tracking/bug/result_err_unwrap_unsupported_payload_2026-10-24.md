# result_err_unwrap_unsupported_payload

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: unsupported Result.err() payload type in backend_plugin/loader.spl load_dynamic_backend_v1 (validated.err().unwrap()).

Workaround (tagged `@workaround bug=result_err_unwrap_unsupported_payload_2026-10-24`): match validated: case Err(e): return Err(e) (src/compiler/70.backend/backend_plugin/loader.spl).

Root fix location: native lowering of Result.err() for nominal-enum payloads in src/compiler/50.mir (Result accessor lowering).
