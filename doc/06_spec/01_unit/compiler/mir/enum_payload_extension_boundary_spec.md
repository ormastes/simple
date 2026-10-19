# Enum payload extension boundary

Authored manual for
`test/01_unit/compiler/mir/enum_payload_extension_boundary_spec.spl`.
REQ-ENUM-COHERENCE-PAYLOAD. Execution and generated documentation: UNRUN.

Register a current HIR enum using production `register_enum_variants`, with
one text-payload variant and one unit variant. Verify the known tuple arity is
accepted before injecting a future payload-kind string. Require exactly
`invalid declared payload kind` for that variant, preserve the unit neighbor,
and require `unknown variant` for a missing variant.

In a fresh registry, missing/extra tuple payloads and an extra unit payload
must return `payload arity mismatch`. An undeclared variant under a different
qualified owner must return `unknown variant`.

The spec checks real boundary methods and exact diagnostic reasons. It does
not compile a mutated compiler, execute native code, or establish general
schema-evolution compatibility. The fixture uses current named HIR fields;
no stale positional constructor is copied from another suite.
