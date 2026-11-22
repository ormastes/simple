# Windows native object cache never hits: AOT object dir split only at `/`

- **ID:** native_aot_object_dir_windows_backslash_cache_never_hits_2026-11-22
- **Priority:** P1 (every Windows native-build; Stage 3 cannot resume a killed native_compile)
- **Status:** fix proposed (`native_aot_object_dir_v1`); not yet verified by a Windows rebuild.
- **Found on:** release `8dae652711e9` Phase 2 compiler, manual Phase 3 compile
  `build/rboot/manual-p3c` (1237 objects emitted, then killed on memory).

## Symptom
Objects named `aot-<64hex>.o` land in the PARENT of `--cache-dir` (here the `-o` directory), not
in the cache scope `<cache-dir>/s<32hex>/`. `build_cache.sdn` records all of them, yet a rerun
reuses none and deletes every entry.

## Root cause
- `driver_aot_native_output.spl:2356` builds `object_base = _sffi_path_join(cache_scope_root, "object")`;
  on Windows `rt_path_join` joins with `\`, giving `C:/.../cache\s6f4...\object`. This was confirmed by
  recomputing the object hash: `sha256("native-aot-object-v1|<len>:C:/.../manual-p3c/cache\s6f4...\object|<len>:<module>")`
  reproduces the on-disk name `aot-0057ca3e...`, while the `/`-joined base does not.
- `native_aot_artifacts.spl:13` takes `std.nogc_sync_mut.path.dirname(object_base)`, which splits only
  at `/` (`path.spl` `rfind("/")`), returning `C:/.../manual-p3c`.
- Lookup: `driver_native_build_filter_scoped_outputs` (`driver_aot_native_output.spl:1649`) requires
  `obj.starts_with(cache_scope_root + "/")`. That fails, so `all_in_scope=false` and the entry is removed
  (`:2726`). The capsule check (`:2667`) recomputes the same out-of-scope path, so the index cannot be
  hand-edited into a hit either: the two checks are mutually exclusive on Windows.

## Fix
`native_aot_object_dir_v1` splits at the last `/` or `\`. The object then lives at
`<cache-dir>\<scope>/aot-<hash>.o`, which passes the scope prefix check. The object identity hash is
unchanged. POSIX paths contain no `\` from `rt_path_join`, so Linux/macOS behaviour is unchanged.

## Spec
`test/02_integration/compiler/native_aot_artifacts_spec.spl`
"keeps objects inside a backslash-joined Windows cache scope": fails on the old `dirname` (object lands
in `C:/build/aot-...`), passes with the fix.

## Not fixed here
`std.nogc_sync_mut.path.dirname`/`basename` still split only at `/`; other Windows callers that feed them
`rt_path_join` output may share this defect class.
