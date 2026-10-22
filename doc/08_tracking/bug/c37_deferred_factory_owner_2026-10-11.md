# Deferred specialization callers used removed owner methods

Issue: https://github.com/ormastes/simple/issues/3046

Actual C36 producer `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`
passed HIR for all 95 modules of the deferred source-object closure, then failed
MIR. Retained evidence is in the C06 worktree under
`build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-sdn-frontend/mono-deferred/error-groups.json`.
The frozen source was the a9b534 manual candidate; the source paths remain in
the receipt and SCV snapshot. No old receipt was overwritten or reclassified.

At C37 source `c9cb8d6ac95ab64c95dc74c46772d2c60002271e`, five deferred paths still
call `SpecializationKey.new`, although types.spl exposes only the free
`specializationkey_new`. These produce ten undefined-variable/unresolved-new
events. `SpecializationEntry.from_key` also calls nonexistent
`key.mangled_name`; the actual implementation is `engine.spec_key_mangled_name`.
The repair imports and calls these owners. It does not change key fields,
type argument order, cache lookup, or mangling policy.

The same metadata entry used an unavailable array clone receiver. A typed copy
now creates a fresh outer argument array with the same ConcreteType element
values. This preserves outer-container independence; it is not a newly promised
recursive deep copy of every nested enum payload. The regression mutates each
outer array independently in both directions.

## Remaining groups and qualification

The retained 32 distinct MIR diagnostics also include GenericTemplate optional
tuple payload ownership, metadata serialization methods, and type_subst
interpolation traversal. This commit does not claim to repair those groups.
They have separate source ownership and must be qualified together only after
review. Source review and native execution remain pending at authorship.

The actual API spec checks canonical empty/nested mangling, metadata isolation,
existing cache hits and name/type-argument misses, and missing-template errors
for all four instantiation entrypoints. No fake owner or compiler stub is used.

Coordinated manual replay entry:
`src/compiler/40.mono/monomorphize/deferred.spl` (and, for the shared metadata
change, `src/compiler/40.mono/monomorphize/metadata.spl`). Use the admitted pure-
Simple producer and exact source/SCV identities, private phase-bound caches,
`SIMPLE_NO_STUB_FALLBACK=1`, and the existing reviewed manual-object harness.
Record HIR, MIR and object outcomes separately. No expensive compile was
launched while available disk was below the required 20 GiB floor.
