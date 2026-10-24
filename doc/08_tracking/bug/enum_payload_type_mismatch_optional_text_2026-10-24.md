# enum_payload_type_mismatch_optional_text

Status: compiler fix committed (unverified: producer not rebuilt).

Symptom: `CompileResult.CodegenError` payload mismatch at 0 (driver_aot_codegen_outputs compile_to_c_directory) for `if val present = cmake_err: return CompileResult.CodegenError(present)` with `cmake_err: text?`.

Repro: test/fixtures/compiler/p3fix_mir/opt. Trace (SIMPLE_ENUM_PAYLOAD_TRACE=1) on the binder: remembered='' source=none; on cmake_err itself remembered='text?'.

Root cause: ExistsCheck (expr_dispatch.spl) recorded a payload type only for Float/Bool/Array/Tuple/Named; a Str payload left the if-val binder untyped, and the raw word is not a text value (needs rt_interp_cstr).

Fix: ExistsCheck keeps Optional(Str) + the present-edge marker; present_collection_binding/decode_present_collection (mir_lowering_stmts.spl) narrow the binder to a real text local, same decode as narrow_optional_text_receiver.

Related false accept (separate bug): text_optional_into_text_payload_false_accept_2026-10-24.md.

## Workaround record (phase-3 adhoc lane, landed with #4302)

Status: workaround applied, root fix open. Found in Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: enum construction 'CompileResult.CodegenError': payload type mismatch at 0 (driver_aot_codegen_outputs compile_to_c_directory); text? narrowed via 'if val' is not accepted as text.

Workaround (tagged `@workaround bug=enum_payload_type_mismatch_optional_text_2026-10-24`): annotate cmake_err: text? and coalesce with ?? to a typed text local (src/compiler/80.driver/driver_aot_codegen_outputs.spl).

Root fix location: src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl: accept narrowed optional binding as its inner type.
