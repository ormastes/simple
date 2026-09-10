# Feature Expert: Environment-Optimized Dynamic Libraries

## Role

Own process knowledge for exact environment admission, catalog-selected sibling
providers, generation-pinned bindings, parser-first SIMD specialization, and
later native/SMF/JIT/GPU placements. Admission compatibility and actual
execution placement are separate decisions.

## Canonical artifacts

- Research: `doc/01_research/{local,domain}/environment_optimized_dynamic_libraries.md`
- Source proposal: `doc/01_research/compiler/simd/simple_environment_optimized_dynamic_libraries_2026-09-07.md`
- Requirements: `doc/02_requirements/{feature,nfr}/environment_optimized_dynamic_libraries.md`
- Architecture/design: `doc/04_architecture/compiler/environment_optimized_dynamic_libraries.md`, `doc/05_design/compiler/environment_optimized_dynamic_libraries.md`
- Plans: `doc/03_plan/compiler/environment_optimized_dynamic_libraries.md`, `doc/03_plan/sys_test/environment_optimized_dynamic_libraries.md`
- Lane: `.spipe/environment_optimized_dynamic_libraries/{state.md,knowledge_selection.sdn}`

## Frozen contracts

`EnvironmentSnapshotV1`, `VariantDescriptorV1`, `BindingPlanV1`, and
`FrontendFacetV1`. Preserve versioned adapters; do not overwrite existing V1
wire records. Use exact architecture-specific features and OS-usable state,
never one cross-architecture numeric rank.

## Invariants

- Eligibility and trust checks precede ranking; inert validation precedes native mapping.
- `prefer`, `require`, and `max` never create capabilities or cross architectures.
- Hot batches use a pinned dense slot with no filesystem/environment/symbol scan or lifecycle lock.
- Metadata, mapping, callable, executed, completed, and retired are distinct receipt states.
- Host parser features never imply generated-code target features.
- Legacy parsing remains the independent oracle until canonical dialect parity is proven.
- GPU is a placement sibling, not a SIMD tier; device claims require correlated fence and retirement evidence.
- Unsupported host/device rows remain blocked with owner and resume evidence; synthetic fixtures are not native performance proof.

## Current phase

Feature A + NFR N2 selected. Stage-1 contracts/admission, the frontend advisory
seam, narrow AVX2 lexical classification, packed completion proof scaffolds, and
cache V2 canonical validation exist. The cache receipt is not yet owner-issued;
Vulkan has no retained fence/lease owner. Production defaults, published ABI,
full parser parity, native SIMD promotion, JIT/AOT materialization, and GPU
execution remain unclaimed until focused evidence passes.

## Update rule

Update this expert map with each pipeline stage, source/spec paths, exact evidence,
open blockers, and resume commands in the same change.
