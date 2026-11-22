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

## Second occurrence: MIR shard workers, `.fpc` read-back (2026-11-22, release `8dae652711e9` Phase 2)
Same variable, different phase. Canonical Stage 3 with `SIMPLE_MIR_SHARDING=1`, pinned
`pinned-8dae652711e9`, log `.simple/storage/build/bootstrap/logs/x86_64-pc-windows-msvc/stage3-native-build.log`:
- **Cold run** (empty frontend cache): shard 0/9 passed 179/180; shards 1/9 and 2/9 then died
  `0xC0000005` at `claimed=0`. Shard 0 was the first process to parse with the cache on, so it wrote
  the `.fpc` entries that shards 1 and 2 read back.
- **Warm run** (caches from the cold run): shard 0/9 died at `claimed=0` immediately
  (`stage3-native-build.log:6647`, `exit=-1073741819 ... ntstatus=0xC0000005`). Lines `6600-6646` show
  `phase2:parse` with `cached=1..4` (every file a frontend-cache hit); the last completed file is
  `src/compiler/00.common/driver_core_types.spl`. So the AV is in parse, on `.fpc` hits, long before
  any MIR claim (`native_mir_shard.spl:6-11`: workers re-run parse/HIR before claiming).
- **Workaround confirmed:** `SIMPLE_FRONTEND_CACHE=0` (`frontend_parse_cache.spl:103`; the HIR cache
  stays on via `driver_hir_cache.spl:130-136`). With it, shard 0/9 passed 180/180 and shard 1/9 got
  past startup on the same tree.
- Ruled out: the Windows backslash `dirname` defect
  (`native_aot_object_dir_windows_backslash_cache_never_hits_2026-11-22.md`). The `.fpc` path is joined
  with `/` (`frontend_parse_cache.spl:150`).

Root cause is still not named: no minidump. Both occurrences are "a process restores
frontend-cache entries written by an earlier process, then AVs". The cross-process `.fpc`
hit-restore path (`frontend.spl:160-172`) is the shared suspect; step 3 above (minidump) still applies.

## Decode-path audit vs. tonight's Phase 2 miscompile families (2026-11-23, read-only)
Source audited: `origin/release/1.0.0` @ `ccb5a2ef29c`. The failing compiler (`8dae652711e9`) is an
ancestor of all three fixes (be3ddb1579b, #10920 `cbeb12ce33f`, #10925 `a8bb3822cf2`).

**Format actually in play: `.fpc`, not `.spab`.** The Stage 3 cache dir
(`.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage3-native-cache/default/frontend`)
holds 1613 `*.fpc` and zero `*.spab`. So the hit is `frontend.spl:156-169`
(`frontend_parse_cache_load` -> `build_module_from_flat_pool_blob`) ->
`module_assembly.spl:1739` `_build_module_from_cache_v1` with `packed = nil` ->
`flat_pools_restore_all` (`module_assembly.spl:1539`, `FlatPoolReader.new_canonical`).

**Route: scoped.** Native-build sets `cli_mode_text = "aot"` (`bootstrap_main.spl:802`), so both the
observation and plain routes reach `parse_full_frontend_selected_v1`
(`driver_source_parse_selected.spl:226`), which wraps the hit in a per-file transient scope and
promotes `ParserModule` + `driver_promote_retained_frontend_owners_v1` before scope end (`:245-273`).

**Crash window (narrowed).** In the warm run the last line is `phase2:parse:file:done` for file 4
(`driver_core_types.spl`, `driver_source_parse_retained.spl:254`), and there is no `[build] done=4` line
(`:302`). Files 1-3 printed both lines. So the AV is AFTER the 4th hit returned and its scope ended,
inside `:255-304`: `par_had_error_get()`, the bucket probe, and `ParsedEntryModuleBox.new(entry_module)` plus
push (`:297-298`). This assumes `[BOOTSTRAP-PHASE]` and `[build]` flush the same way, which `done=1..3`
supports. Not a decode-arithmetic fault: the decode finished and returned a module.

**Known-family audit: no match. Next Phase 2 (a8bb3822cf2) is NOT predicted to clear this AV.**
- `byte_at(..).to_i64()/to_int()` (#10920): zero occurrences in `10.frontend/{core,_FlatAstBridge,frontend*.spl}`.
  The integer decode is `flat_pool_parse_i64` -> `raw.to_i64()` on a whole line (`flat_pool_codec.spl:516`),
  which is not the byte_at shape.
- untyped optional-bool join / `if val b = dv` (#10925): `FlatPoolReader.decode_bool` is `-> bool?` (typed)
  and has no caller on the `.fpc` path. The path's `if val` sites (`frontend.spl:150` spab, `module_assembly.spl`
  `if val view = packed`) bind struct optionals that are nil here, and both ran correctly for hits 1-3.
- `Record?` local reassigned to None (be3ddb1579b): none in the decode path (`var blob_usable = false`,
  `var reader: FlatPoolReader = ...` are non-optional).
- Windows path: `.fpc` path is `dir + "/" + key + ".fpc"` (`frontend_parse_cache.spl:150`), key is xxh3 hex. No
  `dirname`/backslash split on the read path.

**Remaining hypotheses (ranked; none confirmed):**
1. *Ownership across scope end, delayed aliasing.* A hit REPLACES ~92 pool globals with arrays born in the
   transient scope (non-`_into` decoders). Most are reassigned by the next reset (`types.spl:1900-1922`,
   `decl_nodes.spl:1690`, `lock_level_metadata_reset`), so their dead headers are dropped unread, and
   that matches the miss path. The one replaced owner whose reset writes IN PLACE is
   `par_state.par_text_slot` (restored by `flat_pool_dec_text(r)` at `parser.spl:1700`; reset by
   `par_text_slot[0] = ""` at `parser.spl:433-434`). Its three siblings use `_into`. It IS listed in
   `parser_promote_transient_owners` (`parser.spl:233`), which runs when `parser_entered` is true. Hits
   call `parser_init_with_path`, so it should be covered. That makes it a weak candidate, and it becomes a
   strong one only if `parser_initialization_generation_v1()` does not advance on the hit path.
   Discriminator: `SIMPLE_INTERP_TRACE=1` plus an `[owner-promote]` eprint (`driver_source_parse_support.spl:356`) on the warm run.
2. *Box copy walks an unpromoted inner object.* `ParsedEntryModuleBox.new(entry_module)` (`:297`) copies the
   restored `ParserModule`; any inner heap object built by `flat_ast_to_module` from a scope-born text or
   array not reached by `rt_transient_heap_promote(m)` would fault here. That only happens on hits, because
   restored pool texts are slices of the in-scope `blob.split("\n")`, whereas a real parse's texts come from
   the lexer source.
3. `par_state.par_imported_type_names` is replaced by both paths and is absent from
   `parser_promote_transient_owners`. Because the miss path has the same gap, it does not explain a warm-only crash.

**Guard finding (true regardless of root cause).** `scripts/check/check-flat-ast-codec-complete.shs` is RED
on release/1.0.0: `FAIL - 210 pool(s) checked, 5 not round-tripped`. Three are false positives because
the restore goes through `expr_extra_load` / `expr_s_val_load` / `expr_i_val_load` (`_AstExpr/nodes.spl:1710-1719`).
`par_error_records` is excluded by design. `named_type_modules` (`types.spl:801`) is genuinely not encoded,
so a hit leaves it as the previous module's state (wrong-name risk, not an AV). Separately, the in-place
detector (`:174`) matches only `.clear()`, so index-write resets such as `par_text_slot[0] = ...` are a blind spot.

**Next step (unchanged in substance):** capture a minidump of the warm shard-0 crash (`claimed=0` comes in
~1 s, so it is cheap) and run `cdb -z <dmp> -c ".ecxr; k; q"`. Also re-run a sharded Stage 3 with the
frontend cache ON using the a8bb3822cf2 Phase 2, to confirm the prediction above. Keep
`SIMPLE_FRONTEND_CACHE=0` until then. Status stays OPEN.
