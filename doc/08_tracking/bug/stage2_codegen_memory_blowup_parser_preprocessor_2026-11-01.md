# Stage2 native_compile memory blowup attributed to parser_preprocessor (2026-11-01)

- Status: OPEN. **No module-local construct found.** The attribution to
  `parser_preprocessor.spl` is a progress-label artifact. No source workaround
  was applied: nothing exists to work around.
- Severity: P1 (blocks the Phase 3 stage3 build)
- Owner area: `src/compiler/80.driver/driver_aot_native_output.spl` (in-process sequential
  codegen loop / capsule residency) and `src/compiler/70.backend` (LLVM codegen)
- Frozen compiler: `C:/dev/p3new/stage2.exe` (built from `ef0681fc0e1`)
- Related: `stage2_whole_program_mir_memory_growth_2026-11-01.md` (runs 15/16, same signature)

## Observation (run 19b)

`run19b/build.log:63821-63822`: after `native_cache` finished 190 modules, the log shows
`phase=native_compile ... done=0 total=190 current=compiler.frontend.core.parser_preprocessor`
and then `[NATIVE] codegen: 190 uncached module(s), concurrency=1`. Nothing follows. The tree
grew to 96 GB and was killed (`CAP/LIMIT EXCEEDED: 96.13 GB / 3336 s`). No `.o` file or other
cache file under `C:/dev/p3new/cachewp6` has an mtime after 22:20:24, the start of codegen.

## Why parser_preprocessor is not the cause

`current=` comes from `log_build_progress` before `builder.build(...)` runs, so it names
the first queued unit. It does not show which module codegen was in. `SIMPLE_COMPILER_TRACE`
was not set in run19b, so the ICE breadcrumb and `[NATIVE] compiling module:` lines are absent.

The same frozen stage2 binary, with the same target, backend, `--emit-archive` and PATH/CC as
`r11/run.ps1`, ran under `C:/dev/p3new/tools/measure.ps1 -CapGB 16`. Source: `src/compiler/10.frontend/core/parser_preprocessor.spl`.
The file is byte-identical across `640144fa932`, `3273833de3d` and the current tip.

| probe | entry | env | result (measure.ps1, verbatim) |
|---|---|---|---|
| r2 | parser_preprocessor.spl (67 modules) | threads=1, no whole-program | `first_obj_s=-1 total_s=320.0 peak_tree_GB=5.5 objs=0 max_desc=3 killed=False rc=0 cpu_avg_pct=17` |
| r3 | parser_preprocessor.spl | `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`, `SIMPLE_MIR_SHARD_COUNT=8`, threads=80 | `first_obj_s=-1 total_s=505.0 peak_tree_GB=3.48 objs=0 max_desc=2 killed=False rc=0 cpu_avg_pct=15` |
| r4 | parser.spl (123+ modules codegen'd) | as r3 + `SIMPLE_COMPILER_TRACE=1` | `[NATIVE] compiling module: compiler.frontend.core.parser_preprocessor` finished; tree stayed at 1.4-3.1 GB for the following 100+ modules |

(`objs=0` is a measure.ps1 counting artifact: it only counts `*.o` files. The archive
`r2.a` contains `T compiler.frontend.core.parser_preprocessor._pp_preprocess_conditionals_body`.)

## Conclusion

The blowup is shard- or process-level. A 190-module whole-program shard enters
sequential in-process codegen with about 28 GB already resident. The capsule batch and
MIR stay resident (dynload means output format `Both`, which disables staged codegen and
MIR eviction; see the related doc). Memory grows before or while the first unit
is compiled. The 16 GB cap cannot reproduce it, because the shard's resident baseline
alone is about 28 GB.

## Minimal repro (for the fix owner, needs about 100 GB)

`C:/dev/p3new/r11/run.ps1` plus `$env:SIMPLE_COMPILER_TRACE="1"`. The first
`[NATIVE] compiling module:` line, or its absence, shows whether the growth happens
inside a unit's codegen or in the setup before it.

## Next steps

1. Rerun with `SIMPLE_COMPILER_TRACE=1` to see whether the growth comes before the first unit or inside it.
2. Fix in the driver: release HIR/MIR of other shards before `native_compile`, or allow staged
   codegen/eviction for `Both` output. Tracked with the related whole-program memory bug.
