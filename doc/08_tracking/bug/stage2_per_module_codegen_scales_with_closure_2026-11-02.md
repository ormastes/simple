# Stage2 per-module codegen "scales with closure" (~90 s/module): measurement artifact, real cost is 2-27 s and size-bound

- **ID:** stage2_per_module_codegen_scales_with_closure_2026-11-02
- **Priority:** P3 (diagnostic; the hypothesis this doc was opened for is refuted)
- **Status:** open (two small per-module overheads remain, listed below)
- **Binary:** frozen stage2 `C:/dev/p3new/stage2.exe` built from `ef0681fc0e1`
- **Run:** phase-3 run 20: dynload `--emit-archive`, whole-program, 32 MIR shards, `SIMPLE_COMPILER_TRACE=1`, launcher `C:/dev/p3new/r11/run.ps1`

## Claim under test

A shard worker holding ~28 GB was said to spend ~90 s per module in sequential
codegen. Small-closure probes (`C:/dev/p3new/cgprobe/*`) spend ~1.4 s per object.
The suspicion was that some per-module step scales with closure size or worker
state: capsule or storage snapshot, symbol or layout walks, the RTI registry,
cache witness, receipt hashing, or environment identity.

## Evidence: object and receipt mtimes (ground truth)

The `[NATIVE] compiling module:` lines have no timestamps. The 90 s figure came
from `(cap 2919 s - native_compile elapsed_ms 1947 s) / 13 modules`. Those are
two different clocks. The `[build] elapsed_ms` clock starts after process start,
and the cap counts wall time from launch. The phase marker shows the gap: the
cache scope `phase.marker` (written at `aot:native_entry`, elapsed 1891 s) has
mtime 00:12:22, and the last object was written at 00:17:35. That puts about 5 min,
not 16 min, between native entry and the end of the run.

Each `C:/dev/p3new/aot-*.o.capsule-receipt` names its module, so object mtimes
give per-module wall time. The 13 modules match the 13 trace lines, in order.
Codegen time is measured from the previous receipt write to this object write:

| # | module | object bytes | codegen s |
|---|--------|-------------:|----------:|
| 1 | app.io._CliCompile.compile_targets | 248960 | (first, includes capsule freeze) |
| 2 | compiler.driver.driver_aot_native_output | 496120 | 7.9 |
| 3 | compiler.hir.hir_lowering._Expressions.expression_core | 108773 | 5.0 |
| 4 | compiler.backend.linker.coff.coff_link | 241078 | 5.5 |
| 5 | compiler.hir.hir_lowering.types | 68352 | 2.6 |
| 6 | compiler.frontend.core.parser_expr | 74511 | 2.0 |
| 7 | lib.nogc_sync_mut.io.process_ops | 221430 | 4.1 |
| 8 | compiler.mir._MirLoweringExpr.switch_operators_calls | 908645 | 24.4 |
| 9 | compiler.mir_opt.var_reassign_ssa | 132431 | 8.2 |
| 10 | compiler.mir._MirLowering.module_lowering | 523200 | 14.2 |
| 11 | compiler.frontend._FlatAstBridge.convert_nodes | 144800 | 6.6 |
| 12 | compiler.driver.driver_pipeline_lowering | 178535 | 3.9 |
| 13 | compiler.mir._MirLoweringExpr.expr_dispatch | 902165 | 26.8 |

Modules 2-13 averaged **10.6 s** per module. Codegen time tracks object size,
roughly 30-40 KB of object per second for large modules. The object-to-receipt
step (fingerprint plus capsule re-identity) adds 0.3-4.8 s, also size-bound:
908 KB took 4.8 s.

Control from an earlier run on the same binary, with a smaller closure
(`C:/dev/p3new/aot-0bd61d42...o`, 22:26:40 to 22:27:02): a 905 KB object took
**22.6 s**, against 24.4-26.8 s in run 20. Small objects run 1.5-3x slower in
run 20 (2-8 s against about 1.5-2 s), which fits allocator and heap pressure in a
28 GB process. Codegen does not grow with closure size. The ~1.4 s/object probe
figure comes from probes that emit mostly small library modules. Run 20 shards
contain the largest compiler modules: 48 modules, 885621 MIR instructions in
total (`mir_verify: modules=48 ... instructions=885621`).

Native compile started at about 00:13:19 (native entry plus 56.5 s of
`native_cache`). The first object followed about 129 s later. That window
includes `freeze_native_module_capsules_v1` for all 48 modules
(`driver_aot_native_output.spl:2576`), which serializes and hashes each module's
MIR, plus the first module's own codegen.

## Static review of per-module work at ef0681fc0e1

These are the per-module steps in `_compile_frozen_module_capsule`
(`src/compiler/80.driver/driver_aot_native_output.spl:3625`) and
`driver_native_collect_capsule_result_v1` (`:1234`):

1. `capsule.identity_valid()` (`driver_types.spl:173`) re-serializes the whole
   module MIR (`native_capsule_mir_identity_v1`, `driver_types.spl:249`, which
   runs `serialize_mir_function` over every function) and SHA-256s it. It runs
   about 3x per module: through `driver_native_capsule_inputs_valid_v1` before
   codegen (`:1300`), after codegen, and in the collect receipt check (`:1066`).
   The cost is O(module MIR), not O(closure). It explains the size-bound 0.3-4.8 s
   receipt step.
2. `frozen_native_capsule_batch_find_v1` (`driver_types.spl:220`) is a linear
   scan over the shard's capsule batch (48 entries), called twice per module.
   O(shard), which is negligible.
3. `build_cache.save()` (`:1291`) rewrites every cache entry for each module
   (O(entries)). This is already tracked in
   `native_codegen_build_cache_save_retention_2026-10-25.md`. It costs seconds
   at most here.
4. Codegen itself (`compile_module_with_backend_scoped_v1`,
   `70.backend/backend/backend_helpers.spl:397`) gets only the module's
   `MirModule` and storage sites. None of the `_MirToLlvm` iteration walks a
   global registry. The only non-module dict walk is `unknown_func_decls`
   (`core_codegen.spl:608`, per-module). llc runs as a subprocess on a per-module
   IR file (`llvm_backend_tools.spl:280`).

No step was found that scales with closure size or worker RSS. No RTI registry,
symbol-table, or environment-identity walk runs per module.

## Workaround / settings

No environment variable is needed or available to skip the capsule identity
checks. They fail closed by design, and they cost O(module), not O(closure).
For a shard that has to build big compiler modules, the time that matters is
**serial codegen inside one worker**: `concurrency=1`, `build()` runs
sequentially (`:2690-2715`), and `SIMPLE_NATIVE_BUILD_THREADS` has no effect
there. Projections:

- Expected per-module time with the current settings: **~10-11 s average**
  (2-27 s by size), so about **8-9 min per 48-module shard**, not 72 min.
- `SIMPLE_CODEGEN_MODULE_SCOPE=1` (`backend_helpers.spl:405`) frees each
  module's codegen arena. It reduces RSS growth across a shard, which also cuts
  the 1.5-3x small-module slowdown under heap pressure. Expected result:
  **~7-9 s per module**. This is an estimate, not measured.
- To go faster you need more, smaller shards (larger `SIMPLE_MIR_SHARD_COUNT`
  within the memory budget). There is no per-module env switch.

## Follow-ups

- Add a timestamp (`+Nms`) to `[NATIVE] compiling module:` (`:3681`), or log a
  `log_phase` per module, so trace logs give per-module time without reading
  mtimes.
- Compute `native_capsule_mir_identity_v1` once per module and memoize it on the
  capsule for the post-codegen and collect checks (identity of the same frozen
  object).
- Check why run 20 stopped after 13 of 48 modules (the last receipt was at
  00:17:40). That is outside the scope of this doc.
