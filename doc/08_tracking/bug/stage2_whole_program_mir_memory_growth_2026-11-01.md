# Stage2 whole-program memory growth (38 GB -> 66.6 GB), 2026-11-01

- Status: OPEN (diagnosed by static/log analysis only; launch-only workaround proposed)
- Severity: P1 (blocks Phase 3 stage3 build on the frozen stage2)
- Frozen compiler: `C:/dev/p3new/stage2.exe` (built from `ef0681fc0e1`), unchanged across runs
- Source range: `640144fa932` (run 12, peak 38.31 GB) .. `3273833de3d` (runs 15/16, killed at 64.34 / 66.58 GB)
- Logs: `C:/dev/p3new/r11/run12`, `run15`, `run16` (`build.log`, `build.log.err`, `result.txt`, `build.log.cap`)

## Summary

The +28 GB is **not** MIR growth caused by source changes. The MIR phase peaks
at the same RSS at both source revisions. What changed is that run 12 failed
72 MIR lowerings, so go-to-end skipped codegen and the run ended at the MIR
peak. The RTI and stage2 workarounds landed in the range fixed those failures.
Runs 15 and 16 then reached `native_compile`. That phase does sequential
in-process codegen while the full MIR set stays resident: the `dynload` mode
yields output format `Both`, so staged codegen and MIR eviction are disabled.
Memory climbed from about 35 GB to more than 64 GB there.

## Evidence

| Metric | run 12 (640144fa932) | run 15 (3273833de3d) | run 16 (same snapshot) |
|---|---|---|---|
| closure files / modules | 1516 | 1520 | 1520 |
| HIR shard measured worker peak commit | 12.6 GB | 11.4 GB | 14.8 GB |
| `[mir] 1500/N rss_mib` | **35410** (4221 s) | **35313** (3439 s) | not flushed (stderr lost on kill) |
| MIR failures | 72 (E-RTI-004/007, 13 modules) | 0 | n/a |
| reached `native_compile` | no (`0 object(s)`, link skipped) | yes, 106 cached, 1414 uncached, `concurrency=1` | killed at 6127 s, same profile |
| result | rc=1, peak 38.31 GB | killed 64.34 GB at 6623 s | killed 66.58 GB at 6127 s |

Run 15 MIR RSS curve: 23.6 GB @50, 27.3 GB @500, 31.5 GB @1000, 35.3 GB @1500.
That is a base of about 23 GB (HIR and mono) plus about 12 GB of MIR across all
1520 modules. MIR finished at 4474 s and `native_cache` at 4739 s. After the
`[NATIVE] codegen: 1414 uncached module(s), concurrency=1` line, no progress
lines appear for 1880 s while the tree grows from about 35 GB to 64 GB.

Run 12's MIR failures were in these modules: `file_fiber_tldr_bridge_v1` (35),
`io.buffer` (18), `async_ref` (8), `simple_ring` (2), and one each in
`core_codegen`, `interpreter_calls`, `module_callable_types`, `expr_dispatch`,
`serialization.__init__`, `async.poll`, `mutex`, `enum_wire`, `src.map`. The
in-range workarounds made them lower: `e1cb3bd38b0`, `99a45712909`,
`a34322e9e17`, `515f96e824e`, `290304c37e0`, `e5771c867d6` and `404747cc60a`.

Stage2 source that explains the resident set (`ef0681fc0e1`):

- `src/app/cli/native_build_output_plan.spl:8`: `build_mode == "dynload"` with no explicit native emit gives `driver_output_format_both()`.
- `src/app/cli/native_build_output_plan.spl:84` and `src/app/cli/native_build_main.spl:1218-1221`: for format `Both`, MIR sharding is disabled. The log shows `[mir-shard] disabled: output format re-reads MIR set` in runs 12 and 16.
- `src/compiler/80.driver/driver_aot_pipeline.spl:492-494`: staged codegen (flush and release MIR per batch) is refused for SMF, self-contained or `Both` formats.
- `src/app/cli/native_build_main.spl:1186-1189,1253-1255`: `SIMPLE_MIR_SHARD_COUNT` sets the shard count. More shards than concurrent workers queue, so each worker's MIR share shrinks.

## Ranked source suspects (closure roots, `640144fa932..3273833de3d`, 51 commits)

| Rank | Commit | +lines | New closure files | MIR memory impact |
|---|---|---|---|---|
| 1 | `e1cb3bd38b0` + `99a45712909` + `a34322e9e17` + `515f96e824e` + `290304c37e0` + `e5771c867d6` + `404747cc60a` (stage2 workarounds) | ~360 | 0 | **Indirect, decisive.** They turn 72 MIR failures into PASS, so codegen now runs and the full-set codegen footprint shows up for the first time. |
| 2 | `3b94b409c17` fix(generics): one erased body per generic fn (#5732) | 709 | 0 | No measurable effect. MIR RSS at 1500 modules is 35.31 GB vs 35.41 GB, and the per-generic erased body is small next to the ~23 GB base. |
| 3 | `1190624f895` MC/DC module coverage (`src/lib/nogc_sync_mut/mcdc/*`, 5 files) | 1377 | at most 4 (closure grew 1516 -> 1520) | Under 0.1 GB of MIR (about 1377 lines out of roughly 1M in the closure). |
| 4 | `a2001a4129e` macro RR invalidation (`incremental.spl` +338, 3 new cache files) | 844 | ~3 | Negligible (lines only, no generics fan-out). |
| 5 | `1ee539b4a42` generic RR facets (`hir_variant_object_key_v1.spl` new) | 578 | 1 | Negligible. |
| 6 | `8b7b0627b3f` macro RR contract | 295 | 1 | Negligible. |
| - | `178ecc247f1`, `5a90ae258b8` (HM kernels), `e582b77da58` (RTI contract), `597feb125fe` | <200 | 0 | Compile-time logic only. They cannot add tens of GB. |

The whole range adds about 4.6k SPL lines in the closure roots. Even at the
worst observed ratio (about 12 GB of MIR for the entire closure), that is well
under 1 GB. No source-level gate on generic template bodies is warranted for
this incident.

## Workaround (launch only; no source change, no stage2 rebuild)

`@workaround bug=stage2_whole_program_mir_memory_growth_2026-11-01`

Make the stage3 build use the MIR-shard lane, so codegen runs per shard in
workers that exit:

1. Add `--mode one-binary` to the native-build argv. `native_build_output_format_v1("one-binary", ...)` returns format `Native`, so MIR sharding is admitted and staged codegen is eligible. Stage4 already requires `one-binary`, and the stage3 compiler executable needs no SMF side output for Phase 3 (MCP, caret, dev hub).
2. Set `SIMPLE_MIR_SHARD_COUNT=8`. Run 15 had `shards=1`: one worker claimed all 1520 modules, so it held the whole MIR set through codegen, which is the same failure. With 8 shards each worker holds about 190 modules.
3. Keep concurrency at 1. Set `SIMPLE_MIR_SHARD_WORKER_KB=40000000` with the tree budget at 56 GB, so `parallel=1`.

Expected per-worker peak: about 23 GB base, plus about 1.5 GB of MIR, plus
about 1/8 of the codegen growth (about 4 GB). That is roughly 30 GB serial,
under 45 GB. If one worker still exceeds 45 GB, codegen growth is concentrated
in one module, not cumulative. Then bisect with `SIMPLE_MIR_SHARD_COUNT=16` and
the `[mir-shard]` ledger terminals.

Risk: `one-binary` links a single binary without the SMF/dynload side outputs.
If Phase 3 acceptance needs the dynload layout, use this run to unblock object
production. Then re-link dynload from the warm native object cache
(`--cache-dir` is unchanged, so objects are reused).

### Launch delta for `C:/dev/p3new/r11/run.ps1`

```powershell
$env:SIMPLE_MIR_SHARD_COUNT="8"            # was 1
$env:SIMPLE_MIR_SHARD_WORKER_KB="40000000" # was 24000000; forces parallel=1 under 56 GB tree budget
# Rest args: insert after 'native-build':  '--mode','one-binary',
```

## Root fix (later, needs a stage2 rebuild)

- Let `Both` output evict MIR after per-module codegen. Re-derive the SMF side from per-module archives instead of re-iterating `ctx.mir_modules` (`driver_aot_pipeline.spl:492`).
- Find the codegen leak: about 29 GB over at most 1414 sequential modules in one process (`[NATIVE] codegen ... concurrency=1`). Per-module LLVM context and MIR should be freed after each object.
- Make the `[mir]`/`[NATIVE]` progress lines flush to the parent log, so a kill does not lose them (run 16 has none).
