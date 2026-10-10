# Explicit direct-call type transport

This repair preserves existing accepted `callee<T>(values)` syntax so return-only
generics can reach monomorphization with caller-declared types. The bootstrap
MC/DC lock closure is the primary regression. No source syntax extension or
admission bypass is introduced.

The flat expression owner stores type-arena handles in a separate list from
value-expression handles. Allocation/reset, cloning and flat-pool transport own
that list; codec v4 prevents old cached layouts being reinterpreted. Parser
lookahead retains its comparison and const-generic rejection checks, restores
the confirmed checkpoint, and uses the real type parser to capture structure.
Each direct postfix call consumes its pending explicit types exactly once.

The bridge converts type handles into rich Type values in
Expr.explicit_call_types. HIR lowers those Types into the existing Call type
argument list; the monomorphizer remains responsible for exact generic arity
and specialization. Empty lists continue to request inference. Member-call
generic specialization is a separate existing boundary.

Generated traversal visits the extra Type children. Generated semantic hashing
encodes their contents; opaque block-arena handles remain uncacheable when their
AST owner cannot be traversed. Field default initializers must not be mistaken
for type syntax by the schema extractor.

Bootstrap preparation uses the Rust seed only to build the native Simple schema
tool and compiler. Generation and native regression work use those Simple
executables. Compiler preparation must include the selected canonical K1 source
root and runtime binding; missing-composition refusal is preserved.

Status: source candidate, generator output assertions passed, native compiler
preparation underway; no full bootstrap admission.
