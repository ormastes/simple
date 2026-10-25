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

## 2026-09-22 cross-feature integration

`doc/04_architecture/compiler/dynamic_runtime_kernel_provider_composition_2026-09-22.md`
and its detail design/test/agent plans reconcile this selected provider design
with runtime cdylib authority, Cocoa packaging and existing KPF/aspect owners.
This is documentation evidence only. Existing selected contracts and promotion
gates remain unchanged; outstanding aspect options remain unselected. The
retained feature knowledge receipt does not cover OS kernel/driver code, which
requires a refreshed `mdsoc_only` route before implementation.

## 2026-10-24 levelled vector provider (one DSO, one object per SIMD level)
- Code: `src/runtime/providers/vector/vector_level_{private.h,dispatch.c,portable.c}`;
  `bitmap_provider.c` under `SIMPLE_VECTOR_LEVELLED`. Legacy single-ISA builds unchanged.
- Levels follow clang: x86_64 L1 `x86-64`, L2 `-v2`, L3 `-v3`, L4 `-v4` (AVX-512
  intrinsic kernels); aarch64 L1 NEON / L2 SVE / L3 SVE2; riscv64 L1 RVV; L0 = refuse.
  Baseline dispatcher probes once (CPUID+XGETBV, getauxval/elf_aux_info, macOS sysctl,
  RVV prctl), caches atomically; `SIMPLE_VECTOR_MAX_LEVEL` caps link no higher objects.
- Gate: `sh scripts/check/check-vector-provider-levels.shs ABS_OUT [run|qemu|compile|all]`
  (Windows .dll native, Linux .so native, aarch64/riscv64 qemu-user, FreeBSD/macOS/
  Windows-ARM/SimpleOS compile-only). Bench: `src/runtime/test/vector_level_bench.c`.
- Admission roots now include `/usr/local/lib/simple/providers/` (FreeBSD/macOS).
- DB staging: exact-length inputs skip padded copy; readback via `raw_read_u32s`
  (seed DB probe 810 ms -> 2.1 ms/op).

## Status snapshot 2026-10-25

Verified against `origin/release/1.0.0` @ `57a129fb2b9`: V1 contracts and the
composite selector are source-landed (DONE as source); executed provider
selection/ABI/fallback evidence is PARTIAL (system spec bodies still pending);
compile-mode per-module dynlibs and import libraries are OPEN
(`doc/08_tracking/bug/dynload_mode_emits_no_per_module_dynlibs_2026-10-24.md`).
Full table: `doc/03_plan/compiler/environment_optimized_dynamic_libraries.md`.
