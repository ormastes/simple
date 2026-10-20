# Shared nominal body owner

`lean_type_declarations` owns module-admitted names, nominal kinds and exact MirTypeDef values. New sibling `lean_nominal_body` consumes that context and MirFunction; it does not derive names from raw IDs or fabricate a definition. Both retained backend entrypoints invoke it only where a pure body and module context are available.

The emitter has per-function type, assigned and live dictionaries. Instructions produce typed Lean lets after exact MIR checks. A Move consumes its source. All writes are local to the abandoned emitter on error, so no partial function/module result escapes. Existing module APIs retain their builder publication boundary. Standalone calls without module context retain the existing translator's refusal.

No dependency on a new framework, no independent primitive mapper, no new declaration grammar, and no trust manifest change. Physical storage semantics and theorem closure remain separate required work.
