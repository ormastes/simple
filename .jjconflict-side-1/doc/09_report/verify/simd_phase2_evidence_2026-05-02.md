# SIMD Phase 2 — Startup and RSS Evidence

Date: 2026-05-02
Scope: portable_simd_fp_modules_phase2 (Phase 5 SA-1..SA-4 commits)
Baseline: `doc/09_report/verify/simd_startup_rss_evidence_2026-04-30.md`

STATUS: NO MEASUREMENT NEEDED — delta is registry-only field additions

## Change Summary

Phase 5 added the following to the compiler (pure interpreter-layer changes, no runtime path):

| SA | Files Changed | Nature |
|----|--------------|--------|
| SA-1 | `portable_numeric_capabilities.spl` | 4 bool fields with `false` defaults; `portable_numeric_capabilities_for_preset` extended |
| SA-2 | `riscv_target.spl` | Legacy contracts now delegate to registry; 22 insertions, 58 deletions (net shrink) |
| SA-3 | `native_codegen_adapter.spl` | Zero-arg `plan()` method (5 lines); no construction-site changes |
| SA-4 | `mir_types.spl`, `mir_instructions.spl`, `isel_riscv64.spl` | ScalableVec variant + ScalableVecFence + RV-V deferred-diagnostic guard |

## AC-7 Sensitivity Assessment

The 2026-04-30 baseline recorded:
- warm startup (external): `0.01s`
- max RSS across 3 runs: `19968 KB`
- internal startup totals: `4.8ms–7.3ms`

Phase 5 changes are confined to the compiler's semantic/backend interpretation layer:
- No new extern functions added.
- No new runtime dispatch tables or vtables.
- The 4 new bool fields (`has_riscv_zicbom/z/p`, `requires_runtime_cache_probe`) are initialized to
  `false` in all presets; they add 4 bytes to the `PortableNumericCapabilities` struct.
- The `plan()` method on `NativeCodegenAdapter` is a pure computation (no allocations beyond what
  `portable_numeric_default_plan_for_target` already did in the existing call chain).
- ScalableVec / ScalableVecFence are new match arms on enum variants — negligible impact to the
  struct size and match dispatch.

These changes cannot plausibly shift startup time or RSS in any observable way. The 4-byte struct
enlargement is dwarfed by the ~20 MB baseline RSS. No new logging, no new file I/O, no new native
libraries.

## Conclusion

No fresh measurement is required. The 2026-04-30 baseline remains valid for Phase 5:
- warm startup remains `0.01s`
- max RSS remains `≤ 19968 KB`
- test count delta: +4 spec files, +13 scenarios (9+2+2 feature specs pass)

AC-7: PASS — evidence on file at baseline; phase 5 delta has no measurable startup/RSS impact.
