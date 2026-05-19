# SStack State: host-cpu-runtime-variants

## User Request
> next task from the plan — host_cpu_runtime_variants (5 tasks: CPU config, dispatch routing, loader probing, package variants, tests)

## Task Type
feature

## Refined Goal
> Implement host CPU runtime variant infrastructure: CPU feature detection + SIMD tier config, tier clamping/precedence, compiler+runtime dispatch routing, loader suffixed-variant probing with fallback, package multi-variant manifest with round-trip, and verification specs.

## Acceptance Criteria
- [x] AC-1: Host CPU config — detect CPU features (SSE/AVX/AVX2/AVX-512/NEON/SVE), report active SIMD tier
- [x] AC-2: Config clamping — clamp requested tier to hardware-supported max
- [x] AC-3: Tier precedence — tier ordering with fallback chain (avx512 > avx2 > sse4 > scalar)
- [x] AC-4: Compiler dispatch routing — route codegen to active tier based on config
- [x] AC-5: Runtime dispatch consumer — runtime function selection based on active tier
- [x] AC-6: Loader variant probing — probe for suffixed library siblings (libfoo_avx2.so)
- [x] AC-7: Loader probe fallback — fallback chain when preferred variant missing
- [x] AC-8: Package multi-variant manifest — metadata for variant payloads with platform/tier/path
- [x] AC-9: Manifest round-trip — serialize/deserialize variant manifest entries
- [x] AC-10: Verification spec — 20 tests covering config, clamping, dispatch, probing, manifest

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement (Engineer) — 2026-05-18
- [x] 6-refactor (Tech Lead) — 2026-05-18
- [x] 7-verify (QA) — 2026-05-18
- [x] 8-ship (Release Mgr) — 2026-05-18

## Phase Outputs

### 1-dev
10 ACs across 5 plan tasks. 5 parallel agents (A-E). Existing: simd_capabilities.spl, simd_platform.spl, simd_provider.spl in compiler SIMD infra.

### 5-implement
5 parallel Sonnet agents. 5 files created:
- src/lib/nogc_sync_mut/simd/host_cpu_config.spl — SimdTier + CpuFeatureSet + TierClamp + TierFallbackChain
- src/lib/nogc_sync_mut/simd/variant_dispatch.spl — DispatchRoute + DispatchTable + RuntimeSelector + CodegenTierRouter
- src/lib/nogc_sync_mut/simd/loader_variant_probe.spl — VariantProbe + ProbeSequence + VariantResolver + LoaderProbeConfig
- src/lib/nogc_sync_mut/simd/variant_manifest.spl — VariantEntry + VariantManifest + ManifestParser + VariantSelector
- test/unit/lib/host_cpu_variant_spec.spl — 20 tests

### 7-verify
20/20 tests PASS.
