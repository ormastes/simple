<!-- codex-design -->
# Agent Task Plan — Simple Compiler Performance and Memory Efficiency

## Authority

Merge owner and final highest-capability reviewer: `/root`. Generated-manual review owner: `/root`. Sidecars may implement bounded disjoint lanes but cannot change frozen interfaces, accept exclusions, or mark done.

## Dependency graph

```text
W0 baseline/ownership
 -> W1 vector containment + pass contracts
    -> W2 frontend/diagnostics || W3 MIR facts
       -> W4 typed first-release rules
          -> W5 CollectionPlan/COW || W6 pass rehabilitation
             -> W7 CostSummary/.sperf
                -> W8 .sprof-v2/curves/profile ranking
                   -> W9 tool hot paths
                      -> W10 docs/refactor/verify
```

## Frozen shared names

`PassStatus`, `PassExpectation`, `BackendDelegation`, `PassRunRecord`, `EffectivePipeline`, `PerfRuleId`, `PerfDiagnostic`, `OperationSummary`, `CostExpr`, `AnalysisIncomplete`, `PerfFacts`, `LoopFact`, `MemoryRegion`, `PerfSummary`, `CollectionPlan`, `CowUniqueness`.

Frozen manual steps/helpers are those in the system-test plan and `.spipe/.../state.md`. Unimplemented helpers fail explicitly.

## Waves and ownership

| Wave | Owner lanes | Gate |
|---|---|---|
| W0 | merge owner; read-only inventory sidecars | admitted binary, dirty-file ownership, one baseline/provenance ledger |
| W1 | vector containment owner; pass-contract owner; tests-only owner | unsafe rewrite excluded; effective pipeline truthful; sentinel/verifier works |
| W2 | frontend-session owner; diagnostic-contract owner; tests-only owner | one revision owner, exact spans, legacy COLL compatibility |
| W3 | disjoint CFG/dominance, loop/range, def-use/liveness, region/memory, escape/COW lanes; one facade/invalidation owner | one CFG build/revision; unknown fails closed |
| W4 | disjoint copy/COW, collection, materialization/capacity, layout/stack, invariant/allocation rule lanes; one registry owner | first-release positive/suppression/unknown matrix |
| W5 | operation/cost, plan extraction, lowering, COW evidence lanes | only pure proven plans transform; true preheaders and zero-trip safety |
| W6 | one mini-lane per pass in selected order | full activation/differential/idempotence/adversarial/perf gate per pass |
| W7 | summary/cache, remaining rule families, `.sperf`, CI tests | deterministic bounded SCC and confident-only regression policy |
| W8 | profile codec, instrumentation, curves, ranking | v1 compatibility; disabled no allocation/I/O; profiles never legality |
| W9 | lint/LSP/MCP/cache/tool hot-path owners | warm no scan/subprocess; startup/request/RSS evidence |
| W10 | docs/manual/refactor owner then independent verifier | all REQ/NFR evidence current; STATUS PASS required for release handoff |

Shared registries/exports are edited by their single owner only. Sidecars submit integration deltas rather than editing shared files concurrently. No lane introduces `40.collection_plan` or a `65` layer.

## Baseline and verification commands

Use the exact admitted native pure-Simple binary and record its hash/provenance. Baseline focused compiler/lint/optimizer/COW/tool performance before source edits. For every touched `.spl` file, run `bin/simple run src/app/optimize/main.spl <file> --full --level=O3` once after stabilization. Then run focused correctness and the identical performance command once.

Final scope includes `check src/compiler`, `check src/lib`, `check src/app/mcp`, `check src/app/simple_lsp_mcp`, MCP stdio integration, owned-file lint/duplicate checks, direct env/process guards, optimizer integrity, requirement traceability, manual quality, and `find doc/06_spec -name '*_spec.spl' | wc -l` = 0.

## Risk gates

- No bulk pass activation.
- Unknown alias/effect/escape/range/cost rejects transformation.
- No raw runtime/env/process shortcut or Rust/C performance rewrite.
- No machine fix beyond ownership/lifetime/effect proof.
- No performance claim without same-binary provenance and repeated measurement.
- No profile-based semantic authorization.
- No implementation/done mark with fail-fast scaffold or missing manual.
- Maximum three fix/verify cycles per slice; stop and record remaining blocker.
## Active hardening tranche: SSA dominance receipts

- Merge owner: `/root`.
- Parallel review input: `ssa_verifier_design`, `verifier_integration_review`, and
  `architecture_perf_facts` lanes.
- Source owners: `mir_opt/perf_facts.spl` for bounded shared facts and
  `mir_opt/mod.spl` for optimizer-boundary policy.
- Acceptance: reject undefined, multiply-defined, use-before-def, non-dominating, and
  unavailable-dominance flows with stable codes; model call results on the normal edge.
- Performance gate: no verification work in normal builds, no dense liveness matrices in
  the verifier projection, and no definitions-by-uses Cartesian scans.
- Remaining follow-up: opcode typing, ownership, loop-boundary proof, exact module-pass
  outcomes, and admitted runtime differential evidence.
