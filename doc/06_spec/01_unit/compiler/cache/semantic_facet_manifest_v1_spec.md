# Semantic facet manifest V1 — incomplete draft

- Executable: `test/01_unit/compiler/cache/semantic_facet_manifest_v1_spec.spl`
- Requirements: `REQ-CSM-003`, `REQ-CSM-005`, `REQ-CSM-008`, `REQ-CSM-012`, `REQ-CSM-029`
- Evidence class: executable SSpec definition; no execution receipt is embedded.

This diagnostic DTO requires coverage-shaped digests and canonical sorted identities
for callable, field/layout, aspect, macro, and trait facets. The critical
counterexample mutates each of field layout, aspect call signature, macro body,
trait candidate set, and trait absence witness and requires a distinct manifest
digest plus a named diff entry. Empty candidate or absence digest fields are
rejected. Arbitrary well-shaped digests remain forgeable and do not establish a
complete source, candidate, or absence universe.

## Scenario inventory

- targeted field/layout, aspect, macro, and trait digest mutations;
- empty candidate/absence digest rejection; and
- unchanged, insert/delete, coverage, duplicate-order, and profile mismatch
  diagnostic boundaries.

Frozen visible flow: pin one coherent generation; apply one scoped semantic
mutation; recompute the authenticated affected closure; publish or refuse one
coherent generation; verify exact reuse and confined consumer IO. This draft
covers only diagnostic mutation description, not authenticated closure or reuse.

Runtime execution remains unqualified because the selected G integration base
does not contain its imported common-contract closure and no admitted
self-hosted full CLI is available.

This is an incomplete hand-authored draft, not generated-manual qualification.
