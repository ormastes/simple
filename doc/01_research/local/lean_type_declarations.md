# Lean MIR type declarations — local research

2026-10-18. Selected lane: robust-revised-plan.md lane 07, C2 and REQ-MC-007. This packet implements one bounded acyclic declaration step; it does not close C2 or the whole formal feature.

The feature-tree baseline is `/home/yoon/dev/simple-utf8-external-text-root-20261018`. Both `src/compiler/70.backend/backend/lean_backend.spl` and `src/plugins/backend_lean/lean_backend.spl` had a comment-only `export_types`. Both full and regeneration exports invoked it. Existing LeanBuilder structure/inductive emitters are sufficient; no replacement builder or MIR schema is needed.

`src/compiler/50.mir/mir_instruction_graph.spl` owns MirModule.types. `mir_types.spl` supplies authoritative SymbolId, qualified source name, struct field order/type/offset/bit metadata, enum constructor order/discriminant/optional payload, and export identity. The existing `mir_json.serialize_mir_type` retains exact signedness and nominal symbol identity. It is reused instead of creating a third type registry or serialization format.

The actual primitive/body translator is `src/plugins/backend_lean/lean_mir_translate.spl`. The compiler backend imported a missing compiler-local translator; this packet redirects that import to the actual plugin owner. The existing mapper emits exact-width BitVec types and rejects floats, pointers and other unsupported models. It refuses nominal types without declaration context. The new owner-local planner supplies that context to actual module export paths, while direct context-free export retains the old refusal behavior.

Existing Lean backend unit tests include stale primitive expectations and old MirFunction construction patterns. New specs construct current MIR data, use actual module APIs and assert output/error values. They do not treat source scans or a parallel model as runtime evidence. No test or toolchain has been executed for this packet. Existing aggregate-operation lowering and module proof closure remain separate gates.
