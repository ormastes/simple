<!-- codex-design-tldr -->
# Simple Compiler Offload Detail Design — TLDR

- Five frozen contract files: `src/compiler/00.common/structural_contracts/{sidecars,ports,aop,optimizer,offload_profile}.spl`.
- Sidecars, not wider nodes: tags/origins/query-indexes/profile ride content-addressed `ShardRef{ir, snapshot, shard_slot, generation, digest}` shards alongside unchanged Ast/Hir/Mir arenas.
- One `SidecarMapper` per `TransformBoundary` (7 boundaries, lexing→parsing … backend→linker): translates entity refs via `OriginShard`, drops deleted entities, recomputes digest, emits a deterministic `StageReceipt`.
- Ports carry refs + receipts only, never payload or backend fields: `ParsingOutputPort`, `OptimizationInputPort`/`OutputPort`, `LinkingInputPort`.
- AOP (Wave 2) binds pointcuts/advice to QueryIR/MutationIR by digest only (`PointcutQueryRef`, `AdviceTemplateRef`); `rules_enabled == 0` is zero-allocation and bit-identical to AOP-absent.
- Optimizer (Wave 2/3) replaces line-pattern matching with `OptimizationPassContract` (required/produced tags, mutation kinds, legality verifier, cost model).
- Mode is configuration, not a build variant: `CompilerOffloadProfile.stage_modes` (length 8, one per `CompilerStage`) selects `cpu_reference | hybrid_vector_gpu | resident_gpu` per stage; `cpu_only_profile()` never touches GPU.
- `OffloadDecision` mirrors parser framework's `ParseModeDecision`: requested vs selected, single stable `fallback_reason`, `RequireRequested` errors instead of falling back.
- Promotion off `cpu_reference` needs matching identity, parity, and ≥1.5× median speedup evidence.
- Cross-mode parity: all three modes must match `StageReceipt.deterministic_hash` per stage on the bootstrap (stage-3 self-compile) corpus; first divergent stage is the defect site.

```text
CompilerOffloadProfile -> per-stage OffloadDecision -> sidecar mappers at each TransformBoundary -> StageReceipt
```
