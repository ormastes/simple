# text_optional_into_text_payload_false_accept

Status: open (found while reproducing enum_payload_type_mismatch_optional_text).

Symptom: `val e = gen_err(1)` (`-> text?`) then `CRes.CodegenError(e)` into a `text` slot COMPILES on p2shard-6 stage2 and the binary prints a raw handle number (217678222293793) instead of failing or printing "bad". Silent wrong.

Expected: a `text?` value into a `text` payload slot is a type error (or must be narrowed).

Where: enum_payload_local_compatible / lower_declared_enum_payload_expression Str path (src/compiler/50.mir/_MirLoweringExpr/enum_constructor_payload.spl). Not fixed here.
