# Stage 3 surface_build AV at hir_lowering/items.spl (file 189) correlates with a WARM frontend cache, not the whole-program lane

- **ID:** stage3_surface_build_av_items_spl_warm_frontend_cache_2026-11-22
- **Priority:** P2 (Stage 3 whole-program lane on Windows MSVC; workaround W16 in effect)
- **Status:** open. Root cause NOT established: no minidump, no reproduction. This record fixes
  the file index and the variable under test; it ships no source change.
- **Compiler:** admitted Phase 2
  `build/bootstrap/pinned-src/pinned-ac2e90625c2a/.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe`
  (pinned source `ac2e90625c2a`).

## Symptom
`error: native-build worker terminated with Windows native status 0xC0000005 (access violation)
before producing a binary` during `phase=surface_build`. Attempt
`attempts/recovery-threads1-20261122T032834-23196/terminal.stage3-native-build.log` (the same run is
copied as `recovery-threads1-20261122T040011-38186/stage3-native-build.log.before-resume`; full worker
stderr `stage3-native-cache/diagnostics/native-build-stderr-14116-{1,2}.log`). So there is ONE
observed crash, not two.

## The faulting file is 189, not 188
`log_build_progress("surface_build", ...)` (`src/compiler/80.driver/driver_source_parse_retained.spl:391`)
fires only AFTER `entry_surface_builder.add_parsed(...)` (`:384`) returned Ok and the index was
incremented. The last line, `done=188 current=.../src/compiler/20.hir/hir_lowering/types.spl`,
therefore means types.spl COMPLETED. Every run that got past this loop lists file 189 as
`src/compiler/20.hir/hir_lowering/items.spl` (order is the deterministic closure order). The fault is in
iteration 189: the parsed-index lookup (`:344-368`), `entry_modules[...] = parsed_box.value` (`:383`),
or `add_parsed` -> `module_surface_from_module` -> `module_surface_from_owner`
(`src/compiler/20.hir/hir_lowering/module_surface_declarations.spl:391`).

items.spl (26 lines) is unusual: one `use ...module_surface_types.{ModuleSurfaceEnum}` and **15
`export use X.*` glob re-exports**, zero declarations. Of the 188 files that completed, the most glob
re-exports any had was 2 (`10.frontend/core/ast.spl`); zero-declaration modules alone are not the
trigger (19 of them completed).

## The confound: warm frontend cache
| run | env | `[frontend-cache]` | surface_build |
|-----|-----|--------------------|---------------|
| 032834 (crash) | `SIMPLE_BOOTSTRAP=1`, `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`, coordinator, `SIMPLE_NATIVE_BUILD_THREADS=4` | `hits=1609 misses=0 parses=121` | AV at 189 |
| 040011 terminal (pass) | `SIMPLE_BOOTSTRAP=` (unset), direct, threads 1 | `hits=0 misses=1609` | 1609/1609 |
| 024954 (pass) | direct, non-whole-program | `hits=0 misses=1609` | 1609/1609 |

W16's "observed-good config" changed the lane, the route, the thread count AND the cache temperature at
once. The only crash had every module restored from the frontend cache; every pass was a cold parse.
There is no evidence yet for a `SIMPLE_BOOTSTRAP=1`-only code path: the surface builder
(`module_surface_registry.spl`, `module_surface_declarations.spl`) reads no `SIMPLE_BOOTSTRAP*` env,
and the only such branch in `driver_source_parse_retained.spl` (`:465`) runs after this loop.

## Ruled out / checked
- Missing-struct-field class (#10758, `policy.collection`): not present in the surface builder path.
- `if val` struct-Option binding class: the registry builder has none; the `.fpc` hit path
  (`src/compiler/10.frontend/frontend.spl:160-172`) uses the explicit `!= nil` + `.unwrap()` form.
  The `.spab` path does use `if val` (`frontend.spl:150`, `_FlatAstBridge/module_assembly.spl`
  `_build_module_from_cache_v1`), but 1609 successful hits show that binding works in this binary,
  and the warm cache was moved aside before this investigation, so whether the entries were `.spab` or
  `.fpc` is unknown.
- `.spab` mmap texts: `_txt` copies through `rt_string_new` before `flat_packed_close_v1` unmaps, so
  restored texts do not borrow the mapping.

## Next step (cheap, in this order)
1. Re-run the failing config with ONLY the cache temperature changed (whole-program lane, coordinator,
   cold cache) and the reverse (direct lane, warm cache). This isolates the variable.
2. If warm reproduces it: a 2-3 file probe, one module made of many `export use X.*` globs consumed by
   the entry, `SIMPLE_FRONTEND_CACHE=1` with a private cache dir, cold then warm, on a build that routes
   through `driver_source_parse_retained.spl` (`task_total=6` surface_build). Confirm the route first:
   a tiny build may take the streaming/selected path instead and would prove nothing.
3. Capture a minidump (WER LocalDumps or `veh_<pid>.dmp`) and `cdb -z <dmp> -c ".ecxr; k; q"` to
   name the faulting function. None was written for this run.

## Workaround
W16 (`C:/dev/simple-release-boot-20261122/build/rboot/WORKAROUNDS.md`): single direct thread, cold
frontend cache. The cold cache is the part this record expects to matter.
