# SCV retained source observation slice — 2026-10-27

STATUS: IMPLEMENTED_SOURCE_ONLY — execution and feature acceptance outstanding.

The existing compiler `parse_all_impl` now has an explicit compiler-context
`scv_source_observations_v1` selection. It invokes the existing retained parse
loop with a local opaque observation owner; all three original selected
frontend call sites consume the actual result through that owner. The default
route retains its unobserved behavior. BuildRunner files were not changed.

The immutable subject binds the exact retained source inventory and content,
actual driver identity, observation generation and selected frontend context.
Private recording calls the real selected frontend once and samples actual
parsed function names. It produces the existing semantic-query manifest
representation with `Unknown` read coverage, and no semantic authorization.
Public copied DTOs cannot issue or edit the retained receipt's observations.

The receipt rejects changed subjects, duplicate or unobserved source reads,
repeated reads, parse failure, missing observations, stale generations and
closed owners. Unsupported worker, streaming, target-inventory or selected
entry routes fail explicitly. The ordinary retained profile does not infer
resolver or semantic dependency closure from a complete input list.

Tests-first commits: `0f939868b4d`, `c9a151eeba1`, `6f3df24bf14`, `18a3f80bd61`.
The source specification also
covers the existing phase selection, default behavior, immutable projection
copies, actual parser declarations, changed content/inventory/context/driver,
new generation, duplicate input, syntax rejection, unsupported selected entry
and receipt close. A handwritten manual and compiler guide document the same
scope and limitations.

Guide source/API review found no concrete P0/P1 authority issue. Its explicit
public cross-owner loop seam, generation invalidation after default parsing and
error-exit receipt cleanup findings were incorporated. This is source review,
not compiler execution or admission.

Runtime specification execution, SPipe docgen/maintain, branch coverage,
compiler/core/MCP checks and native ownership/performance qualification:
NOT_RUN. No admitted general runtime is available to this lane. No executable
red/green result, verify PASS, full semantic cache acceptance or ready-to-land
status is claimed. Static audits do not replace these missing checks.

Remaining producer work is unchanged: complete authenticated source/resolver
closure, five live semantic owners, owned semantic execution, an issued worker
result, exact full-SCV snapshot correspondence and parent accepted-root
publication. The detailed order remains in
`scv_build_semantic_issuer_producer_blockers_2026-10-27.md`.
