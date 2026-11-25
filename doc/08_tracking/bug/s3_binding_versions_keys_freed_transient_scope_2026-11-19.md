# Stage 3 HIR cache stores freed `Scope.binding_versions_v1` keys (2026-11-19)

## Symptom
Stage 3 (`stage3-i18.simple`, cranelift-built by the integ18 Stage 2 from
release `cbff0ece9e8`) native-builds a stdlib fixture of 87 modules (`use` of
file_ops, external_text, json). With `SIMPLE_HIR_CACHE=1` and the coordinator route,
52 of the 87 HIR cache stores fail. `file_atomic_write` rejects the payload as
non-UTF-8 and the failure is reported as `io-write`
(`driver_hir_cache.spl` store path). The integ18 Stage 2 stores 87/87 on the same fixture.
Every one of the 53 dumped bad payloads fails at a `Scope.binding_versions_v1` key.
The bad keys are raw heap-pointer bytes, `""` or `"1"`, and the value is always 0
(a lookup miss). `Scope.symbols` is encoded first and is intact. Type-name keys are
intact; function- and import-name keys are not.

Impact:
- Plain builds lower these modules again, which is slow.
- HIR shard workers treat the failed store as fatal
  (`driver_hir_pipeline_lowering.spl`).
- A freed key that happens to be valid UTF-8 (`""`, `"1"`) is stored without
  complaint, which corrupts the cache.

## Mechanism (reproduced)
`Scope.binding_versions_v1` (`20.hir/hir_types.spl`) is written by
`advance_binding_version_v1` (`hir_symbol_table_methods.spl:91`) on every define,
unbind and rebind. A dict update keeps the key object it stored first. After
`unbind_local_type` + `rebind_local_type` / `define` with an equal but
distinct text (the import-supersede and own-declaration paths in
`module_import_registration.spl` and `module_declarations_bootstrap.spl`),
the first text object is held only by the version dict. `symbols` holds the
newer object. None of the roots promoted before the per-file HIR scope ends
reaches that first object:
- `hir_module`
- `promote_symbol_table_transient_owners` (`20.hir/hir_lowering/types.spl`): `symbols`, `scopes` and `root_scope_symbols`

So the object is freed and its memory is reused.

Fixture: `test/fixture/transient_scope/binding_versions_first_key.spl`, run with
`check_fx.sh <stage2> <dir> name=<fixture>` and `FX_SRC=<pinned>/src`. On the
integ18 Stage 2 (`cbff0ece9e8`) and the integ21 Stage 2 (`9b0a5cb8aea`), both
cranelift and llvm produce:

```
seed : m0 versions n=3 [alphaA_fn_0=1][alphaB_fn_0=1][alphaC_fn_0=3]
native: m0 versions n=3 [alphaA_fn_0=1][alphaB_fn_0=1][promote =0]
```

The surviving names are also keys in `symbols` with the same object. Only the
unbind/rebind name (`C`) is freed. That matches the dump pattern: a freed key
with value 0, while `symbols` is intact.

## Workaround (this change)
`promote_symbol_table_transient_owners` first promotes each scope's
`binding_versions_v1` dict as its own root. The result is advisory: false
only means the dict is already persistent, which is the state before this change.
The same fixture with this shape is SAME as the seed on integ18 and integ21, on both backends. Each dict promote returned true.
Tagged `@workaround bug=s3_binding_versions_keys_freed_transient_scope_2026-11-19`.

## Open / unproven
- **Why the version dict is not reached.** The walk through `scopes` should reach
  `binding_versions_v1`. It does not, while promoting the dict as a root works. Ruled out:
  - the field default `= {}` (removing it still gives DIFF);
  - copy-on-write of the nested dict write (native aliases `root_scope_symbols`;
    the seed interpreter copies instead, which is a separate interpreter/native
    divergence).
- **Not verified on the real repro.** No Stage 3 was rebuilt with the
  workaround. The 87-module HIR cache repro must be re-run after the next Phase 3
  rebuild.
- **Proper fix.** Either make the version dict reachable from the promoted
  roots, or refresh the stored key on update. Refreshing alone does not cover
  unbind tombstones.

## WA Src Lane 4 Audit & Hardening (2026-11-26)
- **Verified pre-scope allocation mechanism:** `lower_and_check_modules_impl` (`src/compiler/80.driver/driver_hir_pipeline_lowering.spl`) invokes `begin_module` -> `SymbolTable.reset_module()` before `rt_transient_array_scope_begin()`, allocating `Scope(0)` outside any transient scope. Because backends allocate structs via `rt_alloc` (not `rt_struct_alloc`), `Scope(0)` is absent from both `rt_transient_raw_allocs` and `rt_struct_allocs`, `rt_transient_raw_words(Scope(0))` returns `-1`, `rt_core_transient_classify(Scope(0))` returns `0`, and `rt_transient_heap_promote(table.scopes)` stops at `Scope(0)` without descending into `Scope(0).binding_versions_v1` (unlike `table.root_scope_symbols`, which is promoted directly).
- **Hardening & marker grammar fix:** Kept the workaround in `promote_symbol_table_transient_owners` (`src/compiler/20.hir/hir_lowering/types.spl`), moved explanatory comments above `# @workaround bug=s3_binding_versions_keys_freed_transient_scope_2026-11-19 reason=promote_unreached_first_key` so it immediately precedes the affected loop (`workaround_index.spl`), and bound explicit typed locals (`val scope: Scope = table.scopes[scope_id]`, `val binding_versions: Dict<text, i64> = scope.binding_versions_v1`) before `rt_transient_heap_promote(binding_versions)`.
