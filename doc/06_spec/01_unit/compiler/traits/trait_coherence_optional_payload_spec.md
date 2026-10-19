# Coherence diagnostics and optional payloads

Authored manual for
`test/01_unit/compiler/traits/trait_coherence_optional_payload_spec.spl`.
REQ-ENUM-COHERENCE-PAYLOAD. Execution and generated documentation: UNRUN.

1. Register a foreign trait/type implementation with no local types. Require
   exactly one OrphanImpl with nil suggestion and the exact base diagnostic.
2. Register an unrelated local wrapper. Require the same orphan error with
   Some text and the exact two-line suggestion suffix.
3. Register the trait locally, then separately the target type locally. Each
   ownership boundary must suppress the orphan error.
4. Register an inherent implementation without a trait. Require no orphan error.
5. Render overlap, associated-type, and blanket-conflict variants. Require
   exact messages and payload positions; the first two cases cover OrphanImpl.
6. Register 128 local types and two foreign implementations. Require one error
   per foreign implementation in registration order and unchanged registry
   counts. This is bounded behavior evidence, not an allocation/time benchmark.

All scenarios use the production checker and renderer. Unsupported constructor
metadata is covered separately by `enum_payload_extension_boundary_spec.spl`.
