# result_err_unwrap_unsupported_payload

Status: compiler fix committed (unverified: producer not rebuilt).

Symptom: `unsupported Result.err() payload type` (backend_plugin/loader.spl) for `validated.err().unwrap()` with an enum error type.

Repro: test/fixtures/compiler/p3fix_mir/errunwrap. Red on p2shard-6.

Root cause: builtin_result_payload_mir (builtin_method_extras.spl) admitted Struct/Class nominal payloads only; a native enum payload (its own rt_enum_new handle) was rejected.

Fix: admit a registered native enum (enum_constructor_symbol_owner) and mark the payload a runtime value, same as decode_declared_enum_payload_slot.

## Workaround record (phase-3 adhoc lane, landed with #4302)

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: unsupported Result.err() payload type in backend_plugin/loader.spl load_dynamic_backend_v1 (validated.err().unwrap()).

Workaround (tagged `@workaround bug=result_err_unwrap_unsupported_payload_2026-10-24`): match validated: case Err(e): return Err(e) (src/compiler/70.backend/backend_plugin/loader.spl).

Root fix location: native lowering of Result.err() for nominal-enum payloads in src/compiler/50.mir (Result accessor lowering).
