# Nominal MIR body export: local evidence

The selected robust plan's C2 / REQ-MC-007 requires semantic data export. Applied `lean_type_declarations.spl` admits acyclic nominal declarations and resolves signatures, but `lean_mir_translate.spl` still refuses struct/enum Aggregate and GetField. Both backend owners call that translator for pure function bodies. This packet fills that concrete gap for a bounded single-block value subset.

The actual MIR contract uses `MirFieldDef` declaration order, exact retained field types, `MirVariantDef.discriminant`, and an optional single payload type. `mir_verify.spl:check_variant` resolves discriminants rather than array indexes. `MirBody.from_function` takes the signature return type and parameter count. Native physical aggregate allocation remains a separate semantics boundary.

Changes retain the admitted definitions in LeanTypeContext and share one body translator between actual plugin/compiler module owners. Tests call both full and generated module APIs. No compiler, test runner or Lean replay was executed for this feature.
