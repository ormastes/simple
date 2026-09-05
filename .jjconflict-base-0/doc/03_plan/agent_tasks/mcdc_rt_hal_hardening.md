# Agent Tasks: MC/DC, RT, and HAL Hardening

## Frozen shared vocabulary

`McdcMode`, `McdcDecisionId`, `McdcRecorder`, `McdcExclusion`, `RtHalProvider`,
`RtHalComparison`, `EnvAccessInstruction`, `EnvAccessReceipt`. Shared step and
checker names are defined in `.spipe/mcdc_rt_hal_hardening/state.md`; unresolved
oracles must use `fail(...)` or `assert(false)`.

## Serial dependencies and ownership

1. Merge owner freezes common compiler/MIR/HAL/env contracts and diagnostics.
2. Compiler owner lands AST identity, HIR/MIR evaluation probes, then interpreter.
3. Runtime owner may parallelize Pure Simple recorder/analyzer after step 1.
4. Backend owners land static lowering/absence proof, serializing edits to shared
   MIR instruction definitions.
5. HAL and environment owners may independently implement their disjoint trees.
6. RT assurance owner lands profile staging and transitive effects after contracts.
7. AOP/loader owner integrates dynamic activation after compiler/backend/recorder.
8. Merge owner integrates specs/manuals/perf evidence and performs final review.

Boundaries use frozen share/encoded payload/child-owned result and deterministic
parent commit. Queues and memory are bounded. Unrelated generated target deletions
remain outside all lanes.

## Sidecars and review

Read-only parallel lanes completed for architecture, system tests, and detail
design. Implementation lanes may use lower-model sidecars only on disjoint owned
files. Merge owner and final highest-capability reviewer: primary Codex `/root`.
