# RT loop-fact annotation requires its declaration import

Date: 2026-10-17
Bug: BUG-RT-LOOPSITE-IMPORT-20261017
Database registration: pending; no admitted database tool available.
Status: reproduced; source repaired; post-fix native qualification pending.
Affected source: 9c0fd117dabca9513d0dc3b9f6c5e17268264494.
Producer SHA-256: 0015C3FE0DFD28C22E55CBE488636F30E5BAA869D1608CAD4847685B9C553429.

The explicit `val loop: LoopSite = raw_loop` annotation in
`src/compiler/35.semantics/rt_criticality_validation.spl` introduced a named
consumer dependency without importing its declaration. `LoopSite` is declared
and explicitly exported by `compiler.semantics.effect_verifier`; importing
`effect_block_loops` does not import the return element type into this module.

A bounded diagnostic retained the original six source roots, bootstrap entry,
producer and frozen SCV revision. The genuine static HIR shard
`265233999/1000000007` selected exactly the failed module among 1301 paths.
It exited 1 with `unresolved type: LoopSite`, `claimed=1`, `lowered=0`,
`hits=0 misses=1 stores=0`. The full stderr and original failed queue were recorded at
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase3-rt-manual-hir-20261017`
and the adjacent original `phase3-0015-remote-diagnostic-20261017` attempt.

The fix adds `LoopSite` to the existing selected import from its actual owner.
It preserves the annotation, loop body, effects and policy validation. This is
an import repair, not a runtime workaround or permissive fallback.

Regression acceptance: the same compiler must lower the repaired module in the
complete Phase 3 closure, then emit real objects with stub fallback forbidden.
The source edit invalidates the whole closure HIR digest; let the cache owner
create new keys and retain the old records. Frontend cache reuse must be
reported from actual counters. No object, link or full runtime qualification
is claimed by the source repair alone.

## Current remote follow-up: 2026-10-18

Reviewed remote release_phase3 `2414f2755c76f1d22ffdceb546657db442d7e68d` still imports only LOOP_BOUND_NONE, while its actual consumer annotates `val loop: LoopSite = raw_loop`. The current effect_validation owner declares `effect_block_loops(block: HirBlock) -> [LoopSite]`; effect_verifier declares and explicitly exports LoopSite. This establishes the missing declaration import without relying on a broad diagnostic-tree replacement.

This isolated follow-up extracts only that one-line import and this dated report from dfcfc9017fff1457316feb13dcb0411fb6b8dd20. No RT body, failclosed policy, newer remote implementation or unrelated agent work is replaced. The historical raw diagnostic directory named above is no longer present at review time; its prior observations are preserved as historical evidence, not claimed as newly reproduced or currently available logs. Database reconciliation remains pending.

Frozen candidate74113 already includes this import and is undergoing separate qualification. Its progress does not qualify this current-remote PR. Focused/native and required compiler/lib/MCP/LSP checks remain UNRUN until a qualified source-matched normal CLI is available. No heavy build, native execution, Rust seed fallback or repeated green runtime check is performed for this source-only follow-up.
