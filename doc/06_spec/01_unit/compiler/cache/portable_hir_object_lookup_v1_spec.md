# Portable HIR three-payload object lookup V1

Executable source:
`test/01_unit/compiler/cache/portable_hir_object_lookup_v1_spec.spl`.

## Contract

Three-payload consumers derive lookup identity from the complete immutable
`PortableObjectRefV1`: content digest, stage, portability, IR schema, required
semantics digest, optional target contract, and verification-receipt digest.
Changing semantic or verifier provenance therefore cannot alias an existing
symbolic-body lookup.

The HIR profile delegates to that common key and does not open body bytes.

## Authority status

Lookup identity is copied data, not authority. Physical TLD framing and its
canonical verifier are absent from this slice, so semantic-verifier and
completeness availability remain false. Encoding, verification, and native
loader admission stay closed.
