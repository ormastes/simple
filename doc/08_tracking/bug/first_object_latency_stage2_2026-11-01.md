# First object takes 121-364 s with the frozen stage2, even for 1-object closures

- **ID:** first_object_latency_stage2_2026-11-01
- **Priority:** P2 (perf; the user's rule is first `.o` within 10 s)
- **Status:** partially fixed (shard fan-out clamp landed; SCV warm refresh + pre-closure window remain), re-measure with stage3
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

## Split measurement, 2026-11-02 (lane mp-4)

Frozen stage2 (ef0681fc0e1), `src/app/dashboard/main.spl` (1-file closure), same flags
as the cgprobe, fresh worktree `C:/dev/wt/mp-4`, wall clock from a timestamped stdout/stderr
relay (`C:/dev/p3new/mp4probe/tsprobe.ps1`) plus `SIMPLE_INVENTORY_TRACE_ATTEMPT` cost lines.

| run | SCV inventory | SCV snapshot | first .o | result |
|---|---|---|---|---|
| fresh checkout, `COLD_INIT=1` | 135.5 s (44,036 files hashed: src+test+examples) | 252.9 s (14,991 files materialized) | 485 s | rc=1 |
| warm cache, `COLD_INIT=1` (cgprobe config) | 102.1 s | 8.2 s | 205 s | rc=1 |
| warm cache, no `COLD_INIT` | 8.4 s | 8.7 s | 103-124 s | rc=1 (MIR shard aggregate failure) |
| warm, no `COLD_INIT`, parse+MIR shards off | 8.4 s | ~9 s | **74 s** | out.o written |

Findings:

1. **The cgprobe's ~145 s pre-driver time is mostly its own `SIMPLE_SCV_INVENTORY_COLD_INIT=1`.**
   Forced cold init re-lists and re-hashes every `.spl` under `src`, `test` and
   `examples/10_tooling` (~100 s warm cache) on every run. A first build in a checkout already
   auto-cold-inits (`source_authority.spl`, no cursor -> cold); probes must not force it.
2. **Shard fan-out ignored the closure size.** A 1-file closure spawned 8 parse, 5 HIR and 5 MIR
   shard processes. Each child pays ~4-5 s start plus ~3.7 s `load_sources` before claiming its
   one unit, which is ~50 s, and the MIR shard pass failed the build (`empty mir_modules`).
   **Fixed:** the coordinator now reads the published closure's selected count
   (`SIMPLE_PARSE_CLOSURE_SELECTED_COUNT`). Closures of up to 4 files
   (`SIMPLE_SHARD_SMALL_CLOSURE_MAX`) run in process, and larger closures never get more
   shards than files (`native_build_shard_count_for_closure_v1`).
3. **aop_weave is not a cost.** It short-circuits when nothing needs weaving (`config.enabled`
   false): about 1 ms per process. The 6 s "aop_weave" window in the first table is the gap
   between interleaved shard-process log lines.
4. **Runtime object cache is shared already.** The cgprobe pins `SIMPLE_RT_OBJ_CACHE_DIR` to
   one directory. No runtime C rebuild showed up in the warm timeline.

Remaining (not fixed here, still above 10 s on stage2):

- 0-3 s process start; 8.4 s warm SCV inventory refresh plus 8.7 s snapshot reopen (both
  scale with the `--source` roots, not with the closure).
- About 23 s between the SCV cost line and `[parse-closure] parent_walks=1`. The frozen stage2
  does not emit the coordinator `build-trace` lines, so this window is not split yet. Candidates:
  `native_build_warm_receipt_prepare` and the closure walk's snapshot open.
- About 26 s in the in-process worker (load_sources ~3.7 s, HIR, MIR, LLVM).

Measure again with the next stage3 build; the shard clamp only takes effect in a binary
built from this source.
