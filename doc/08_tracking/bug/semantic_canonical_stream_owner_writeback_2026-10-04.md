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

Caller-audit correction, release `d8680fe6ec21` (2026-10-04): the prior text
incorrectly identified `src/compiler/80.driver/cache/gateway/declaration_semantic_issuer_install_boundary_v1.spl`
as a production caller. Its references are comments describing a future
integration. The file imports only `ThreePayloadFallbackV1`, reports unavailable
and returns `AuthorityUnavailable`; it has no stream calls or transitive writers.
The five retained live capabilities are still required. Do not activate this
boundary or replace its admission with a digest to manufacture an API migration.

A source-wide search for canonical begin/write/end/finish call syntax outside
the stream implementation found no production calls at that revision. The
current migration surface is the core and executable specs, principally
`test/01_unit/compiler/cache/semantic_canonical_stream_v1_spec.spl`.
The adjacent `declaration_semantic_issuer_install_boundary_v1_spec.spl` should
continue asserting the closed boundary. This correction narrows the caller
claim; it does not dismiss the core owner-transition defect or establish runtime
evidence. New production integration requires a fresh caller/admission review.

Audit owner/session: `/root/linker_research`, `item4-semantic-issuer-owner-20261004`;
isolated sparse worktree `C:/dev/simple-item4-semantic-issuer-20261004`, branch
`work/item4-semantic-issuer-owner-20261004`, base/expected target `d8680fe6ec21`.
No issuer source changes; core and spec ownership remain with their parallel
agents. Sidecars N/A; all runtime verification remains UNRUN.

Regression contract: exact domain/schema header bytes and digest vector; scalar
and nested container digest vectors; byte/item/work budgets cumulative across
successive calls; first error sticky; root arity enforced; close-container updates
parent; first finish succeeds once and second finish rejects on the same owner;
late mutation leaves digest unavailable. No compile-compatibility shim may silently
retain discarded mutations. SHA API migration must remove stale imports/calls but
must not be reported as fixing this independent semantic ownership defect.
