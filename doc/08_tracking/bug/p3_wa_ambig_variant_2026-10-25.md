# P3 WA: bare enum variant reported ambiguous in MIR (`WA-P3-ambig-variant`)

Stage3 per-file MIR (build/s3-perfile2, stage2 @ d72188e68ec) rejects bare `Ok`/`Err`/`Tuple`/`Struct`
patterns when the match subject's type is lost (generic fn in `unsafe(...)`, trait-dispatched
method return) or is Optional (`HirEnumPayload?`): "bare variant X is ambiguous ... has type known non-enum type".
Cascade: "enum construction: missing runtime identity for 'HirTypeKind'" (8).
Emitter: src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl (enum match resolution).

Real fix: feed the declared (substituted) callee return type / binding annotation to the bare-variant
resolver, unwrap Optional subjects, and hard-fail before identity lookup.

WA sites (qualified variants, semantics identical):
- src/compiler/20.hir/hir_codec_support.spl — hc_enc_enum_bool/text/char, hc_restore_enum_nil
- src/compiler/70.backend/backend/backend_helpers.spl — compile_module result match
- src/compiler/70.backend/backend/backend_api.spl — CompilerBackend.compile
- src/compiler/40.mono/monomorphize/hir_subst/body_subst.spl — hs_enum_payload, hs_pattern_payload
- src/compiler/40.mono/instantiation.spl — compile_template result match
