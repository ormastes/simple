# Stage3 parse_full_frontend_selected_v1 returns a Result whose tag is neither Ok nor Err

- **ID:** s3_parse_selected_result_freed_by_transient_scope_2026-11-02
- **Priority:** P1 (every stage3 parse-fiber and hir-shard child panics, so the hello smoke fails)
- **Status:** open. Diagnosis is not yet confirmed. The tagged workaround is in `driver_source_parse_selected.spl`; no stage3 has been rebuilt with it yet.

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
