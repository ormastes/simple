# Parse shards repeat complete source closure

The retained early Phase4 Cranelift full-CLI log contains 115 complete
2,460-module source closures and five allocation failures. Buffered output does
not establish simultaneous worker counts or an allocator leak. The diagnostic
runner disabled host memory admission without a tree budget; no RSS/commit
samples identify the actual peak.

The parent already publishes frozen SCV authority. Each parse child nonetheless
computes the entry BFS, then asks the source loader to walk imports again before
partitioning parse work. The isolated fix publishes a typed immutable selection
and request before parse startup. Children check request SHA, actual entry/roots,
invoking producer SHA, snapshot/generation, actual handed-off policy and every
source's admitted SHA/byte count. The loader retains the complete selection and
existing source-owner finalization. Full/group routes reject this request.

This patch targets parse shards. HIR and final-worker repeated discovery remain
separate work; do not claim all 115 walks eliminated. It does not enforce RSS or
make requested 80 codegen jobs safe as 80 frontend owners. Existing memory
admission and actual enforced bounds remain independent requirements.

Validation: scoped whitespace PASS. Added unit selection identity/membership
negative specs and physical exclusive publication/stale/missing receipt specs are
UNRUN. Native resource admission and actual closure counters/RSS measurements
are pending. No product/admission or measured performance PASS claimed.
