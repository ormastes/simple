# Parse-shard rotation can admit an alias as the canonical module

Status: source repair implemented; admitted runtime verification pending.

Evidence: GitHub run `45128297579`, source revision
`3b51e37a2c1322c644ccaaae3c6c6e3d928ede19`, retained log
`build/verify/p2-sharded-attempt-45128297579/diagnostics/evidence/step.log`.
Phase 2 rejected `src/compiler/10.frontend/core/parser_identifiers.spl` with
`module_name=compiler.core.parser_identifiers` and the correct path-derived
`compiler.frontend.core.parser_identifiers` identity. Source loading completed
2172 rows; a parse shard failed during surface admission.

The source collector lists the canonical row before compatibility alias rows.
Streaming parse shards rotate that inventory by their strided start and claim
physical paths. A rotated walk can encounter an alias before its canonical
row, so the empty shard registry attempts a fresh canonical admission using
the alias spelling. The module-surface guard correctly rejects it. Changing
parser imports or relaxing the guard would conceal the inventory-order defect.

The repair computes authoritative first-row indices once by canonical physical
path, then rotates only those original row indices for cache warmup. It keeps
the original inventory and ordinary canonical/alias admission unchanged, and
preserves physical claim keys, cache identities and successful native cache
artifacts. The plan uses one map pass plus one ring pass, with O(N) expected
time and O(N) space. No per-row inventory scans or filesystem reads are added.

Regression: `test/01_unit/compiler/driver_parse_shard_rows_spec.spl` covers an
alias at the rotation boundary, interleaved aliases, distinct paths, empty and
single-source inventories, and wrapped starts. These specs have not executed
on an admitted runtime in this session. No bootstrap retry or cache deletion
was performed for this repair.

The same retained log independently records MIR Result/Optional declaration
ownership failures at `_AstExpr/nodes.spl:503:19`; this source-row repair does
not establish that those failures are resolved.
