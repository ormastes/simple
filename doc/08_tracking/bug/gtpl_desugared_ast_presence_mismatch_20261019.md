# GTPL wire presence disagrees with desugared AST fields

Status: source repair, runtime UNRUN. FunctionDef stores has_return_type plus text and all Function/Struct/Class/Enum definitions store has_specialization_of plus text. The existing writer passed payload alone into an optional serializer; the decoder passed optional payload into text and omitted required flags. Inherited source fixtures repeated that stale shape. This invalidated source-only extraction integration assumptions; independent review cycle1 caught it.

Repair existing wire boundaries, not the AST/schema: flagged writer emits existing0/1 plus length-prefixed text without an intermediate Option. Decoder converts presence and uses empty payload for absent. Present empty text remains distinct from absent. Noncanonical optional tags reject with a concrete offset diagnostic, preserving transaction rollback. Five fields across four AST kinds are covered by real serializer/deferred APIs and existing later-record rollback.

Wire GTPLv2 and ENV2 markers remain unchanged. All remote byte-concat workarounds remain. No per-template cache, extra file copy, ownership transfer, producer build or native admission is introduced. Runtime memory/performance remain unmeasured; all specs UNRUN.
