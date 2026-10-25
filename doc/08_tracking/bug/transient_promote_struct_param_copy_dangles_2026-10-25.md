# Transient promote of a struct root promotes a copy; the original dangles

- **Status:** fixed in source (`mut value: T` on both promote wrappers). Phase 3
  Stage 3 objects patched by hand for run-27 (see "Delivered objects"). No
  compiler change.
- **Severity:** P0. Every Stage 3 `native-build`, hello world included,
  SEGVed about 70 s in.

## Symptom

Stage 3 (`S/r27/stage3/simple`, sha 06217ffd) SEGVs in `rt_strlen` from
`compile_source_inventory_apply_cold_events_v1`. Its `events` array
(len 42,778) holds `RtCoreString` path objects, not `CompileSourceEventV1`
structs, so reading `event.source_identity` at +16 hands path bytes to
`rt_interp_cstr`.

## Root cause

`src/compiler/50.mir/_MirLowering/transient_owner_sffi.spl:40` (before the fix):

```
fn transient_heap_promote_v1<T>(value: T) -> bool:
    unsafe(capabilities: [ffi]):
        rt_transient_heap_promote(value)
```

`rt_transient_heap_promote` (`src/runtime/runtime_native.c:3153`) retags the
objects it reaches **in place**, starting from the root it is given. With
`T = CompileSourceEventV1`, the mono instance `transient_heap_promote_v1$T1`
gets the Bug #167 defensive copy of a plain value-struct parameter
(`function_lowering.spl:724`, `copy_struct_value_recursive`). The prologue
does `rt_alloc(72)` and copies all 9 fields, so the extern receives the
**copy**. The copy's text children are promoted, but the original struct
shell is allocated in the transient scope and never visited. The shell is
freed by `transient_array_scope_end_v1()`, and
`compiler_inventory_file_event_v1` (`inventory_scratch.spl:29`) then returns
`Some(event)`, which is a dangling pointer.

gdb on the native probe (Stage 2 compiled):

- promote received `0x…ce11`: the copy, with byte_count 3878.
- `Some(event)` wrapped `0x…b5a1`: the original. Its words 0 and 1 had
  already been overwritten by the allocator.
- `rt_array_push` received `0x…b5a1`. Read back, it gave
  `byte_count=80` and garbage `operation`.

In the 42,778-row cold loop, the freed 72-byte shells were reused by later
path strings. The push, the `!` unwrap and `text_arg_indices` are all
correct.

Stage 2's own (seed-built) `transient_heap_promote_v1` is a plain forward
with no copy. The defect appears only in code that the pure-Simple compiler
emits.

The same defect exists in `transient_promote<T>(value: T)`
(`src/lib/nogc_sync_mut/sffi/transient.spl`). A scan of the 1,459 run-27e
objects found 14 struct instances that copy before promoting (they reference
both `rt_alloc` and `rt_transient_heap_promote`):

- `transient_heap_promote_v1$T1` (CompileSourceEventV1)
- `transient_heap_promote_v1$T24` (MirModule, `module_lowering.spl:2389`: every MIR module promote)
- 12 `lib.nogc_sync_mut.sffi.transient.transient_promote$…` instances:
  - ScvCompileMaterializedSourceV1
  - NativeBuildParseClosurePublicationV1
  - DriverHirArchiveJournalStoredEventV1
  - RtBlobDeclarationCensusV1
  - RtBlobFunctionFactsV1
  - OptimizationReqLevel
  - T213, T412, T734, T759, T816, T887

## Fix

Both wrappers now take `mut value: T`. A `mut` parameter is bound by
reference (`is_mut_param`, `function_lowering.spl:673`), so the extern sees
the caller's root. The fixed instance is a pure forward: no `rt_alloc`.

Not done, and deliberately so: eliding the Bug #167 copy for parameters that
are never mutated would need escape analysis. That is a possible follow-up,
not part of this fix.

Latent sites with the same signature that showed no copying instance in
run-27e. Each is `@always_inline` or instantiated only with handles:

- `_sffi_transient_heap_promote` (`hir_lowering/_Items/lowering_helpers.spl:53`)
- `_hir_diagnostic_promote_raw` (`hir_lowering/types.spl:25`)
- `_aspect_registry_promote_raw` (`10.frontend/aspect_registry.spl:45`)
- `_effect_registry_promote_raw` (`10.frontend/effect_registry.spl:44`)
- `_layer_eq_registry_promote_raw` (`10.frontend/layer_eq_registry.spl:36`)
- `_rt_criticality_promote_raw` (`10.frontend/rt_criticality_registry.spl:9`)
- `_promote_bootstrap_registry` (`50.mir/mir_data.spl:1505`)

Direct `rt_transient_heap_promote(x)` extern calls are unaffected, because
extern calls never copy.

## Evidence (Stage 2 `S/r27/stage2-simple`, native, aarch64)

The probe is `p9`: the two wrappers on a struct built inside the scope,
followed by allocation churn.

| build | result |
|---|---|
| wrappers without `mut` | SEGV (rc 139) |
| wrappers with `mut` | `mir n=8 intact=8`, `lib n=8 intact=8`, rc 0 |

On the real path, `compiler_inventory_git_events_v1(... ["examples/10_tooling"], cold=true)`:

- without the fix: SEGV in `spl_str_concat` with `x0 = "examples"`;
- with the fix: 251 events, all with correct op, identity and byte_count.

Spec: `test/01_unit/compiler/50.mir/transient_promote_struct_root_spec.spl`.
The interpreter has no transient arena, so the round-trip examples are
meaningful only natively. The source-contract example pins `mut`.

## Delivered objects (run-27 Phase 3 relink)

- `transient_owner_sffi` and `sffi.transient` cached objects: the 14 copying
  definitions were renamed `…$unfixed_copy` with objcopy.
- 14 one-function fix objects: each is a Stage-2-compiled fixed forward
  (localized, renamed to the instance name).

All are listed in `S/r27/fixed_objs.txt` under `pushunwrap.*`.

## Separate finding (not this crash)

An unannotated local bound from `f()!`, where `f() -> [Struct]?`, loses
element struct provenance. `v[0].field` reads field 0 (resolve_field_index
default) or the raw handle as i64 (about 2e14). Annotating the local
(`val v: [S] = f()!`) or consuming the value through a typed parameter or
match decodes correctly. Recorded in
`doc/08_tracking/bug/unwrapped_optional_struct_array_elem_provenance_2026-10-25.md`.
