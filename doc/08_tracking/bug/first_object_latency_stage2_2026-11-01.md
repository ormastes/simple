# First object takes 121-364 s with the frozen stage2, even for 1-object closures

- **ID:** first_object_latency_stage2_2026-11-01
- **Priority:** P2 (perf; the user's rule is first `.o` within 10 s)
- **Status:** open, re-measure with stage3
- **Owner area:** `src/app/cli/native_build_main.spl` startup (SCV admission/inventory), runtime object build, `src/compiler/80.driver` front phases
- **Found by:** phase-3 codegen probes, 2026-11-01 (`C:/dev/p3new/cgprobe/<name>/`), frozen stage2 `C:/dev/p3new/stage2.exe` (ef0681fc0e1), tip 3273833de3d

## Measurements (measure.ps1 wall clock, `native-build --entry-closure --emit-object`, 8 threads)

| Probe entry | objects | first .o (s) | total (s) | peak tree GB |
|---|---|---|---|---|
| src/app/dashboard/main.spl | 1 | 158.1 | 169.8 | 2.09 |
| src/compiler/00.common/api_surface_contract.spl | 1 | 168.5 | 180.0 | 2.13 |
| src/lib/common/serialization/__init__.spl | 1 | 121.5 | 132.8 | 2.02 |
| src/app/cli/arch_check.spl | 95 | 177.3 | 255.0 | 6.29 |
| src/compiler/50.mir/enum_pattern_physical_v1.spl | 124 | 364.3 | 530.2 | 10.2 |

## Phase breakdown (dashboard, driver `[build]` elapsed_ms, first -> last sample)

| phase | start ms | end ms |
|---|---|---|
| load_sources | 0 | 1355 |
| parse / surface_* | ~2300 | ~2650 |
| hir | 2543 | 4764 |
| monomorphize | 4647 | 4766 |
| mir | 7101 | 7101 |
| aop_weave | 7105 | 13067 |
| native_cache / native_compile | 13447 | 13451 |

The driver phases take about 13 s, and about 6 s of that is aop_weave even with 0 modules.
The remaining ~145 s of the 158 s happens before the driver's `load_sources`: SCV
source-inventory cold init (`SIMPLE_SCV_INVENTORY_COLD_INIT=1`, hashing every file under
the `--source` roots, earlier measured at 400-550 s on full roots), process startup, and the
runtime C object build.

## Suspected causes (ordered)

1. SCV inventory hashes all of `src/lib`, `src/compiler` and `src/app` for a 1-file closure
   (known open item: "SCV hash only own roots").
2. Runtime object build is not cached across probes (`SIMPLE_RT_OBJ_CACHE_DIR` is per run).
3. aop_weave has a fixed ~6 s cost with nothing to weave.

## Next

Re-measure with the stage3 binary (same probes) and split the pre-driver time with
timestamps. If SCV still dominates, scope the inventory to the entry closure.
