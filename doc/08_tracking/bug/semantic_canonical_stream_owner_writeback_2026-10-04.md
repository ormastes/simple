# Semantic canonical stream loses owner transitions across free functions

Status: confirmed source-shape defect against documented class value semantics;
runtime reproduction UNRUN. Inspection base: release `f5fec9ccf8c`.
Separate from the SHA-256 compression/stream owner repair.

Owner: `src/compiler/00.common/cache_contract/semantic_canonical_stream_v1.spl`.
The language guide `doc/07_guide/language/capability_library_authoring.md`
requires mutating `me` methods and warns that copied class receivers discard
scalar updates. No generic reference alias guarantee is assumed.

Concrete affected transitions:

- `_fail_v1` writes the first error into a free-function parameter.
- `_precharge_v1` writes encoded bytes/items/work counters without returning owner.
- `_attach_precharged_v1` increments root count and appends frame children.
- Container begin/end and public write helpers transitively mutate that copied
  owner; changing only the leaf SHA update call cannot repair the outer state.
- `semantic_canonical_finish_v1` writes `finished`, charges work and records sticky
  errors without propagating the owner to its caller.
- `_append_tag_v1` takes a byte-builder value and calls its mutating append method;
  the caller's builder is not explicitly written back, risking missing tag bytes.

Consequences include absent persistent budget charges, missing root/container
state, lost sticky errors, wrong canonical header data and repeat-finish behavior.
These are source-derived failure predictions, not observed execution results.

The smallest complete repair keeps constructors, read-only observers and pure
encoders free, but makes every mutating/transitively mutating semantic operation
`me` on one named mutable stream. Use mutable builder receivers and a builder
`me append_tag` or pure returned byte array. Explicitly store extracted frame
values back into the frame array; keep SHA as a mutable owned field. Preserve
the frozen wire schema and existing independent digest vectors.

Known production caller: `src/compiler/80.driver/cache/gateway/declaration_semantic_issuer_install_boundary_v1.spl`.
Migrate its own transitive free writers, not only direct SHA calls. Relevant
tests: `test/01_unit/compiler/cache/semantic_canonical_stream_v1_spec.spl` and
`declaration_semantic_issuer_install_boundary_v1_spec.spl` in the same directory.

Regression contract: exact domain/schema header bytes and digest vector; scalar
and nested container digest vectors; byte/item/work budgets cumulative across
successive calls; first error sticky; root arity enforced; close-container updates
parent; first finish succeeds once and second finish rejects on the same owner;
late mutation leaves digest unavailable. No compile-compatibility shim may silently
retain discarded mutations. SHA API migration must remove stale imports/calls but
must not be reported as fixing this independent semantic ownership defect.
