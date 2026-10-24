# for_in_optional_variant_payload_binder_i64

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: for-in over non-array (#143), collection mir type I64 in generated/hir_visitor.spl:188: optional variant payload binder (StringLit interpolations) is I64.

Workaround (tagged `@workaround bug=for_in_optional_variant_payload_binder_i64_2026-10-24`): iterate (opt ?? []) as hir_codec.spl does.

Root fix location: src/compiler/50.mir/mir_lowering_stmts.spl (#143) and optional payload binder typing; also the generator that emits src/compiler/20.hir/generated/*.spl. Same shape exists in other generated files (hir_hash/hir_visit/hir_children use match, hir_codec uses if val).
