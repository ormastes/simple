<!-- codex-architecture-tldr -->
# Simple Compiler Offload Architecture — TLDR

The Simple compiler's stages (lex→parse→type→HIR/MIR→optimize→codegen→link) keep unchanged primary IR arenas; tags/origins/indexes/profile ride as content-addressed sidecar shards crossing each boundary via a deterministic `SidecarMapper`. `CompilerOffloadProfile` picks `cpu_reference`/`hybrid_vector_gpu`/`resident_gpu` per stage as config, not a build variant — one binary, `cpu_reference` never deleted, all modes hash-identical.

## Contract groups (`src/compiler/00.common/structural_contracts/`)

- `sidecars.spl` — `ShardRef` + `TagShard`/`OriginShard`/`QueryIndexShard`/`MirProfileShard`.
- `ports.spl` — view descriptors, per-stage ports, `TransformBoundary`, `SidecarMapper`, `SidecarError`.
- `aop.spl` — opaque `PointcutQueryRef`/`AdviceTemplateRef` handles into QueryIR/MutationIR (Wave 2).
- `optimizer.spl` — `OptimizationPassContract`, `EffectSummary`, `OptimizationRemark` (Wave 2/3).
- `offload_profile.spl` — `CompilerStage`, `OffloadMode`, `CompilerOffloadProfile`, `OffloadDecision`.

## ADRs

- ADR-OFF-1 — Sidecars, not wider nodes.
- ADR-OFF-2 — Ports carry refs + receipts only, no `rt_*`, no backend fields.
- ADR-OFF-3 — Opaque QueryIR/MutationIR handles, bound by digest.
- ADR-OFF-4 — Mode is config, not variant; `cpu_reference` is the oracle.
- ADR-OFF-5 — Fallback observable via `OffloadDecision`; `RequireRequested` errors.
- ADR-OFF-6 — Evidence-driven promotion (identity + parity + ≥1.5× speedup).

## Wave mapping

Wave 1: `sidecars.spl`/`ports.spl` + mappers for all 7 boundaries, CPU-only, deterministic receipts. Waves 2-3: `aop.spl` + `optimizer.spl` consumers (tagging/query/mutation features). Waves 4/9: hybrid then resident execution; `gpu_mmu` lane owns placement.

## Open Next

- [Full architecture](simple_compiler_offload.md)
- [Implementation plan](../03_plan/platform/structural_compute/simple_compiler_offload_plan.md)
- [Parent architecture](compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md)
