# Simple Compiler Offload Plan (SIMPLE lane)

**Date:** 2026-07-31 · **Status:** Proposed
**Parent:** architecture doc Part III (§11) and §29 Wave 2/4/9. The Simple
frontend rides on the parser framework (`parser_framework_plan.md`); the
Clang/LLVM bridge (`clang_bridge_plan.md`) is a separate C/C++ lane, not this
one.

## Scope

Offload of the **Simple compiler itself**, per the §11.5 stage × mode matrix:

| Stage | `cpu_reference` | `hybrid_vector_gpu` | `resident_gpu` |
|---|---|---|---|
| file/hash/cache | host I/O | SIMD + batched GPU hash | SSD/direct-to-GPU artifact batches |
| lex/structure | current canonical CPU | SIMD/GPU classify + scans | resident token/structure arenas |
| parse | canonical parser | CPU region parser over accelerated tokens | eligible GPU region parsers, CPU fallback |
| semantic/type | CPU | GPU indexes/bulk probes, CPU decisions | resident tables + eligible graph passes |
| HIR/MIR | CPU | bulk transforms/analyses on GPU | resident SoA transforms |
| optimize | current pass manager | cost-selected GPU query/analysis/mutation | resident QueryIR/MutationIR passes |
| codegen | current backends | selected GPU code/object prep | resident device-target pipelines |
| link | current SMF/native | GPU symbol/layout/reloc batches (link lane) | resident SMF linker (link lane) |

Plus the structural upgrades that make offload possible:

- **Sidecars, not wider nodes:** Ast/Hir/Mir TagShard + OriginShard +
  QueryIndexShard; every MDSOC transform boundary gets a sidecar mapper
  (lexing→parsing … backend→linker).
- **AOP upgrade (§11.3):** `pc{...}` → QueryIR; one evaluator replaces the
  duplicated interpreter/compiler text matchers; `attr`/`within`/`execution`/
  `call` become real structural ops; advice = MutationIR templates;
  `proceed()`-exactly-once as a mutation validator; zero cost when no rules
  are enabled.
- **Optimizer upgrade (§11.4):** keep manifest/pass registry; replace
  line-pattern source matching with QueryIR; `OptimizationPassContract`
  (required/produced tags, mutation kinds, effect, legality verifier, cost
  model); remarks as structured tags; hotness mapped to source via
  MappingGraph.

## Variable execution config

The mode is **configuration, not a build variant** — one binary, selected per
stage via `ExecutionProfile` (SDN profiles, architecture Appendix D):

```text
full offload    resident_gpu   (fallback: hybrid → cpu_reference)
balanced        hybrid_vector_gpu (fallback: cpu_reference)
cpu only        cpu_reference  (no GPU dependency; always available)
auto            policy selector over measured crossover curves
```

`cpu_reference` is never deleted and must run on machines with no GPU at all.
All three modes produce identical artifact hashes.

## Owned paths

```text
src/compiler/60.mir_opt/structural_adapter/
src/compiler/85.mdsoc/feature/tagging/
src/compiler/85.mdsoc/feature/query/
src/compiler/85.mdsoc/feature/mutation/
src/compiler/85.mdsoc/transform/**/sidecars/
src/compiler/90.tools/aop adapters (QueryIR/MutationIR frontend)
test/01_unit/compiler/structural/
```

(Frontend canonical arenas belong to `parser_framework_plan.md`; SMF link to
`link_manager_plan.md`; placement to `gpu_mmu_plan.md`.)

## Dependencies

- Frozen structural contracts (arch §26); QUERY/MUTATE/ID-TAG/MAP lanes.
- parser_framework lane for lex/parse acceleration.
- gpu_mmu lane for resident tiers only — Waves 1–2 are pure CPU.

## Phases

1. **Sidecar ports (Wave 1).** Extended feature ports
   (`ParsingOutputPort`/`OptimizationInputPort`/…); sidecar mappers at every
   transform boundary; deterministic receipts.
2. **AOP migration (Wave 2).** Pointcuts to QueryIR, missing selectors
   implemented, advice as MutationIR. Gate: existing AOP tests + new
   structural selectors pass; no-weaving binary/MIR parity when disabled.
3. **Optimizer migration (Wave 2).** Structural source/MIR selection; profile
   loop (instrument → profile → map → select → mutate → verify → benchmark).
4. **Hybrid acceleration (Wave 4).** Hash/lex/structure SIMD-GPU; bulk
   semantic probes; cost-selected optimizer analyses.
5. **Resident compilation (Wave 9).** Multi-file resident sessions: arenas,
   indexes, IR sidecars stay in Object VM; host gets receipts/diagnostics.
   Gate: bounded host RSS on a 10× corpus; cross-mode hash parity.

## Acceptance

- CPU/hybrid/resident artifact hash parity on the bootstrap corpus
  (stage-3 self-compilation as the end-to-end fixture).
- AOP: around-`proceed` cardinality verified; zero inactive-path allocation.
- Optimizer: before/after semantic equivalence, pass-order determinism,
  remark/hotness source mapping.
- Multi-file cache invalidation closure (separate content/parse/semantic/
  impl/codegen hashes, §9.5).
- Every fallback carries a reason receipt; `cpu only` config runs with no GPU
  present.
