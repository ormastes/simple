# native-build SCV cold init crawls: coordinator module is JIT-demoted to pure interpretation (todo 478)

- **Date:** 2026-11-27
- **Status:** OPEN (root cause localized, not fixed)
- **Host:** Windows 11, seed `C:/dev/keep/seeds/simple-local-20261127h.exe`, worktree `C:/dev/lanes/c27-race` (release/1.0.0 tip 2cc4149be75)
- **Todo:** 478 (`dir_sync` native-link smoke)

## Symptom

`SIMPLE_SCV_INVENTORY_COLD_INIT=1 <seed> native-build <entry> -o <exe>` never reaches link.
It is NOT specific to the `dir_sync` entry: the trivial entry `fn main(): print("hi")`
stalls identically. The long silent period is not a hang and not a git/`workarounds:` scan.

## Where it stalls (measured)

1. Frontend load of the coordinator closure prints ~7,976 `[visibility-warning]` lines, then
   `workarounds: incomplete coverage; run simple check-dbs --fullscan bugs`
   (`src/app/cli/native_build_main.spl:2694`). This line is only a progress marker, it returns promptly.
2. With `SIMPLE_BUILD_TRACE=1` the next and LAST line ever printed is
   `[build-trace] +0ms coordinator:admission root=... source_roots=src/app,src/lib,src/compiler,...`
   (`native_build_main.spl`, just before `compiler_source_authority_acquire_v1`).
   So the stall is inside SCV admission: cold-init inventory
   (`compiler_inventory_refresh_*` in `src/app/compiler_entrypoint/inventory_events.spl`:
   `git ls-files -t ...` then one read + canonicalize + 5 digests per source file,
   47,230 `.spl`/`simple.sdn` files, 341 MB, under roots `src,test,examples/10_tooling`).
3. The process is one busy core (CPU-time +20 s per 20 s wall), no child processes, WS ~2.0-2.5 GB.
   After the reads finish the process keeps burning CPU with 0 read/write ops (post-listing phase).

## Root cause evidence: same code, at least 14x slower (42 s vs >10 min unfinished) once the coordinator closure is loaded

| run | engine | result |
|---|---|---|
| probe A: tiny script calling only `compiler_inventory_refresh_v1(cold_init=true)` | hybrid JIT (only demotion: `hybrid-interp-splice rt_time_monotonic_ns`) | **valid=true, 42,033 ms**, ~1,100 files/s |
| probe B: same call, but script first imports/uses `app.cli.native_build_main` | whole module demoted to the interpreter | still unfinished after >10 min; reads at ~30-90 files/s, then CPU-only tail |
| real `native-build` (3 runs) | same demotion | >8-34 min, never finishes |

Probe B and the real run log, before any inventory work:

```
[engine-demotion] reason=jit-compile-error detail=HIR lowering error: Unsupported feature:
  cannot infer field type while lowering Pointcut.matches_name: struct 'ANY' field 'kind'
  [in src/app/cli/native_build_main.spl]
```

`Pointcut` is defined three times (`src/compiler/10.frontend/core/aop.spl:77` struct,
`src/compiler/35.semantics/aspect_seal/facet_model.spl:93` class,
`src/lib/nogc_sync_mut/src/aop.spl:24` struct); the seed's HIR lowering resolves `self` of
`Pointcut.matches_name` to `ANY`, the JIT compile of the entry module fails, and the seed
demotes (announced by one `[engine-demotion]` stderr line) the entire module (including SCV inventory hashing of 47k files) to the
tree-walking interpreter. Renaming only core `Pointcut` -> `CorePointcut` (experiment, reverted)
removes that message but the next one appears immediately:
`CODEGEN-AMBIGUOUS-METHOD in 'simpleos_sdk_ledger_decode_v1': bare method 'as_str' has 4 candidates [MacroConstValu...`
-- i.e. a chain of independent JIT-compile failures, not one. Caveat: slowdown is attributed to
demotion by correlation (A vs B) and the engine-demotion log; no profiler is available here
to prove the per-phase split.

## Not the cause (ruled out)

- git subprocess / `workarounds:` / check-dbs scan: no children, returns before the trace line.
- Cold-init inventory itself: 42 s when JIT-hybrid (matches the 2026-11-07 round-15 80 s figure
  in `windows_scv_inventory_cold_init_untracked_walk_slow_2026-09-13.md`).
- Why a `dir_sync` entry pulls in `src/compiler/80.driver`: SCV roots are
  `src/app,src/lib,src/compiler,src/os,src/plugins` for ANY entry, and the coordinator itself is
  Simple code importing `compiler.driver.*`; so every native-build loads the compiler closure.

## Next steps

1. Make the coordinator JIT-clean (fix the `Pointcut` ANY resolution AND the `as_str`
   ambiguity at `simpleos_sdk_ledger_decode_v1`; re-run until `[engine-demotion] reason=jit-compile-error`
   no longer appears for `native_build_main.spl`), or
2. Run SCV inventory in a separate lightweight process/script (probe A shape) instead of the demoted coordinator, or
3. Have the seed fail hard instead of demoting for the native-build coordinator.
Repro for the measurement: call `compiler_inventory_refresh_v1(root, root + "/build/scv", ["src","test","examples/10_tooling"], true)` from a script with and without importing `app.cli.native_build_main`.

## Related
- `doc/08_tracking/bug/hir_type_inference_any_field_2026-05-02.md` (same `struct 'ANY' field` lowering failure class).
- `doc/08_tracking/bug/browser_4k_whole_module_dejit_name_collisions_2026-10-04.md` (whole-module de-JIT caused by name collisions).
