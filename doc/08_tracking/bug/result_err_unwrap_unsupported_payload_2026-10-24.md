# result_err_unwrap_unsupported_payload

Status: compiler fix committed (unverified: producer not rebuilt).

Symptom: `unsupported Result.err() payload type` (backend_plugin/loader.spl) for `validated.err().unwrap()` with an enum error type.

Repro: test/fixtures/compiler/p3fix_mir/errunwrap. Red on p2shard-6.

Root cause: builtin_result_payload_mir (builtin_method_extras.spl) admitted Struct/Class nominal payloads only; a native enum payload (its own rt_enum_new handle) was rejected.

Fix: admit a registered native enum (enum_constructor_symbol_owner) and mark the payload a runtime value, same as decode_declared_enum_payload_slot.
