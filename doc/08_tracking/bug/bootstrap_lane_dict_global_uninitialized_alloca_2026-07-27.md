# Bug: module-level Dict global lowers to uninitialized alloca in the stage-4 bootstrap lane

**Date:** 2026-07-27
Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Area:** native codegen / MIR lowering (module-level global initializers, bootstrap lane)
**Severity:** High — segfaults on first read, no compile-time diagnostic

## Status update (2026-07-27)

Downgraded to **unconfirmed** — the isolating experiment that would confirm
"uninitialized alloca" as the mechanism was never run. The original evidence
was a stage-4 segfault at the first `hir_registry_contains` call on a
Dict-typed module global, attributed to the global's backing storage never
being zero/empty-initialized. But the registry that replaced it
(`module_registry.spl` rewritten on parallel `[text]`/`[Module]` arrays,
commit `797497d757bd`) was itself built to route around a DIFFERENT theory —
the struct-field map-copy defect in
`doc/08_tracking/bug/native_struct_field_map_copy_nilfills_nested_dicts_2026-07-27.md`
— which has since been shown not to reproduce. The underlying cause of the
original Dict-global segfault may equally be the now-confirmed
`Dict<K, StructValue>.get()` corrupt-Option defect (see
`doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
and `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`)
rather than a global-lowering/alloca-initialization problem at all.

Separately, an isolated probe of cross-module ARRAY globals (accessor
functions, `[text]` payload) PASSED — `len=2` and correct element reads — so
the array-typed global-lowering path is not in question. What remains
unconfirmed is specifically the Dict-typed case: a dedicated minimal probe
(`module-level var g: Dict<K,V> = {}`, read through an accessor before any
write, isolated from the registry/import-resolution machinery entirely) has
not been run and is needed before this claim can be trusted.

## Finding (original — see status update above)

A module-level `var g: Dict<K,V> = {}` in a module compiled in the stage-4
bootstrap lane lowers to an **uninitialized alloca** — the initializer never
runs, so the first read through an accessor function dereferences stack
garbage and segfaults.

Array-typed module globals (`var g: [T] = []`) already work correctly for
this same lane — that class of bug was fixed 2026-07-25 (commit
`952d2ca34d7`, per project memory); `bootstrap_globals.spl` in
`src/compiler/50.mir/_MirLowering/` is the proven-working pattern for
array-typed globals. The Dict-typed case was never covered by that fix and
still hits the uninitialized-alloca path.

Observed 2026-07-27: the first cut of
`src/compiler/20.hir/hir_lowering/module_registry.spl` (built as the
workaround for the struct-field Dict-copy defect, see Related) used a
module-level `Dict` global to hold the registry. Stage-4 repro18 segfaulted
at the first `hir_registry_contains` call (`hir_done=0`), i.e. immediately
after phase 2 completed and before any registry entry had been written by
this run — consistent with the global's backing storage never having been
zero/empty-initialized. Rewriting the same API on parallel `[text]` /
`[Module]` arrays (commit `797497d757bd`) removed the crash class entirely
with no other change to call sites or logic.

## Repro

Stage-4 bootstrap build of a module that declares a module-level
`var g: Dict<K,V> = {}` and reads it through an accessor function before any
write. Reference repro: `module_registry.spl` pre-`797497d757bd` (git history
— the Dict-global version segfaulted at the first `hir_registry_contains`
call in stage-4 repro18; the array-rewritten version in the current tree does
not).

## Suggested fix

Extend the module-global MIR lowering that already handles array-typed
globals (see `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl`) to
cover Dict-typed globals in the bootstrap lane, so the initializer actually
runs before first use. If full support is not immediately practical, fail
closed: emit a compile error for Dict-typed module globals in the bootstrap
lane instead of silently emitting an uninitialized alloca that segfaults at
runtime.

## Related

- `doc/08_tracking/bug/native_struct_field_map_copy_nilfills_nested_dicts_2026-07-27.md`
  — the defect this Dict-global workaround was built to route around;
  `module_registry.spl` exists specifically to sidestep the struct-field
  Dict-copy bug.
- `src/compiler/50.mir/_MirLowering/bootstrap_globals.spl` — the proven
  working pattern for array-typed module globals (commit `952d2ca34d7`).
- `src/compiler/20.hir/hir_lowering/module_registry.spl` — current
  array-based implementation (commit `797497d757bd`), post-workaround.
