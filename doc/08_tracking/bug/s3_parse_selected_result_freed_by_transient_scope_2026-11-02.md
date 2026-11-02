# Stage3 parse_full_frontend_selected_v1 returns a Result whose tag is neither Ok nor Err

- **ID:** s3_parse_selected_result_freed_by_transient_scope_2026-11-02
- **Priority:** P1 (every stage3 parse-fiber and hir-shard child panics, so the hello smoke fails)
- **Status:** open (stage2-only miscompile, 2026-11-02 static verdict). Current source is not buggy; the tagged re-box workaround stays until a stage3 is rebuilt by a correct stage2.

## Symptom
`panic: called `.unwrap()` on an Err Result` in s3 children (`[parse-shard] shard=1/4 FAILED`, `[hir-shard] failed_workers=4`).

## Evidence
The diagnostic relink `C:/dev/p3new/linkdry/s3bt.exe` (spl_panic renamed with llvm-objcopy, plus a backtrace shim) shows the panicking callers:
- `src/compiler/80.driver/driver_parse_shard_entry.spl:293`, `selected.unwrap()` in `_driver_run_parse_fibers`
- `src/compiler/80.driver/driver_source_parse_retained.spl:242`, `selected_entry_module.unwrap()` in `parse_all_retained_observation_v1`

Both unwrap the result of `CompilerDriver.parse_full_frontend_selected_v1` (driver_source_parse_selected.spl:163).
In the disassembly, is_err tests `rt_enum_discriminant == 1` and gets false, while unwrap requires `== 0` and panics. So the
discriminant is neither 0 nor 1.

## Suspected cause
On the AOT path, `parsed` is created inside the transient parse scope. It is promoted with `rt_transient_heap_promote(parsed)`,
then the scope is ended with `driver_end_transient_parse_scope()`, and then `parsed` is returned. If the promote misses the
Result box, the scope end frees it. This is the same family as #5753 (promote_transient_owner), which the frozen stage2 still has.

## Workaround (drafted, tagged)
After the promotes and before the scope ends: re-box the Result via `match` on the paused heap, promote the payload, and
return the re-boxed value. With `SIMPLE_P3_PARSE_DIAG=1`, a diag prints is_ok/is_err before and after the scope ends.

## Blocker
The one-module rebuild (entry src/app/p3_parsesel_obj/main.spl) peaked at 14.3 GB. The 8 GB probe cap killed it
(cgprobe/parsesel_obj).

## Removal condition
A stage3 built by a stage2 with the #5753 fix produces valid Results without the re-box.

## Verdict (2026-11-02): stage2-only MISCOMPILE, not a source bug
Static analysis of origin/release/1.0.0 (f5b32bda67c), tip df3a14d194b and frozen stage2 ef0681fc0e1:

1. **Same source works under a correct compiler.** The function body is byte-identical between stage2 source
   (`ef0681fc0e1:src/compiler/80.driver/driver_source_pipeline_parsing.spl:472-503`) and tip
   (`df3a14d194b:src/compiler/80.driver/driver_source_parse_selected.spl:163-203`); only the scope wrappers were renamed
   (`driver_parse_transient_scope_begin_v1`/`_pause_v1` in `driver_source_parse_support.spl:162-166` just forward to
   `_sffi_transient_array_scope_begin`/`_pause`). The seed-compiled stage2 runs this exact code on every retained parse
   that builds s3, and it returns valid Results. Only the stage2-compiled copy (in s3) fails.
2. **The runtime promotes the outer box.** `rt_transient_heap_promote` (`src/runtime/runtime_native.c:3340`) classifies
   the root with `rt_core_transient_classify` (`:3132`). A registered `RT_VALUE_HEAP_ENUM` becomes
   `RT_CORE_TRANSIENT_ENUM` (`:3185`), the root is added to the plan, and the payload is walked (`:3403-3404`). A
   persistent registered root is a no-op success (`:3346-3361`), and its memory is not owned by the scope. Either way the
   box cannot be freed by `driver_end_transient_parse_scope()`. The pure-Simple lane
   (`src/runtime/simple_core/core_memory.spl:458`, enum kind 4 walks `rt_enum_payload`) behaves the same.
3. **No compiler-inserted promotion is needed.** The promote is explicit in source. MIR/codegen does not have to
   promote a returned value implicitly.
4. **#5753 is not a codegen fix.** #5753 (88bc2edede3, `50.mir/_MirLowering/transient_owner.spl`) promotes the
   MirLowering roots `rti`, `rti_last_error`, `runtime_value_extern_abis` and `erased_callback_record_bindings`. It is a
   runtime-ownership fix inside the compiler program for the gap that #5709 (33bba69184f) introduced. Neither #5709 nor
   #5753 is an ancestor of ef0681fc0e1, so stage2 never had the rti gap. s3 has both. The earlier "#5753 promote gap in
   frozen stage2" hypothesis is therefore wrong as a cause.
5. **No transient runtime change in the window.** `git log ef0681fc0e1..df3a14d194b -- src/runtime/runtime_native.c`
   has no promote, classify or scope-end change (they are fs/process/console fixes only).
6. **The ownership check passed.** In the failing run the ownership panic (`result_ok ... ended`) did not fire, so
   `rt_transient_heap_promote(parsed)` returned 1. Under the rules above, a 1 can only mean that the root was promoted,
   that it was persistent, or that it was not a heap value at all (`:3368-3381`). The last case is possible only if the
   compiled code passed something other than the enum box: a stage2 codegen error. The function moved to a new module
   (`pub me` in `driver_source_parse_selected.spl`), so in s3 it is a cross-module `Result` return compiled by stage2.

Behavioral spec: `test/01_unit/runtime/transient_scope_result_return_spec.spl` runs the original pattern without the
re-box (begin, build `Result<ScopedPayload, text>`, pause, promote, end, return) and checks the tag and payload fields
after memory churn. Execution evidence: a standalone copy of the spec (same functions plus a `main`) printed
`OK name=mod_main count=2 items=2 alpha_one beta_two` and `ERR-OK rejected_target` under the seed
(`bin/simple.exe run`). That run used the INTERPRETER and did not exercise the native arena. `--native` on the seed failed
with "codegen: IO error: program not found" (no linker on this host). `s3.exe` has no `test` command. The native run is
still pending: run this spec with the next correct stage2 or stage3 test runner.

Removal condition (revised): a stage3 built by a stage2 from source at or after df3a14d194b, without the re-box, returns
valid Results from `parse_full_frontend_selected_v1`, and the behavioral spec passes natively.
