# Bug: native struct-field Dict copy nil-fills nested Dicts in Map values (HirLowering.modules_by_name)

**Date:** 2026-07-27
**Status:** Open
**Area:** native codegen (struct/aggregate deep-copy of Dict-valued fields)
**Severity:** High — silently corrupts import resolution across the whole HIR pipeline

## Finding

Assigning a `Dict<text, Module>` into a struct field
(`HirLowering.modules_by_name`, set in
`src/compiler/20.hir/hir_lowering/types.spl` `hirlowering_for_module`) deep-copies
the map in a way that **nil-fills every `Module` value's nested Dict fields**
(`functions`, `classes`, `structs`, `enums`, `traits`, `constants`) while
**array fields** (`function_order`, `imports`, `exports`, `impls`) survive the
copy intact.

The source map (`ctx.modules` in the driver) stays fully intact — reading
`ctx.modules[name]` directly gives real, populated dicts. Only the copy that
lands in the `HirLowering` struct field is corrupted.

Proven 2026-07-27 by get-vs-index instrumentation during stage-4 bootstrap:
get-vs-index logging on the same typed receiver fetched from the copied field
showed `[getvsidx] idx_fns=-1 idx_forder=9` — the Dict field decodes as empty
(-1) while the parallel array field (`function_order`, len 9) reads correctly
on the identical `Module` value. Meanwhile `lower_module` compiled real
function bodies from the direct param in the same run, confirming the
underlying data was never actually missing — only the struct-field copy of it.

**Consequence:** HIR import resolution (`register_imported_symbol` and
siblings in `module_lowering.spl`) only ever read modules through the
corrupted `HirLowering.modules_by_name` field, so every import resolved
through the phantom-Some decode accident documented in
`doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`.
That bug's "Round 5" section names this same defect as its root cause.

## Repro

Stage-4 native-build of `src/app/cli/main.spl` (full closure, llvm backend) —
instrument `hirlowering_for_module` in
`src/compiler/20.hir/hir_lowering/types.spl` to log both:
- `ctx.modules[name].functions.len()` (direct index read, pre-copy)
- `self.modules_by_name[name].functions.len()` (post-copy struct-field read)

for the same module name immediately after assignment. The index read is
positive; the struct-field read is -1 (nil-decoded), while
`self.modules_by_name[name].function_order.len()` on the same value reads
correctly. A minimal isolated repro (a `struct { m: Dict<text, S> }` where `S`
itself has both a `Dict` field and an `[T]` field, assigned then read back
through the struct field vs. a plain local) has not yet been built — the
stage-4 instrumentation above is the only proven trigger so far.

## Suggested fix

Root-cause and correct the native deep-copy of struct values containing
`Dict`-typed fields (runtime clone routine or codegen copy path — likely in
the same family as MIR/codegen aggregate-copy lowering). Needs isolation with
a minimal `struct { Dict<K, S> }` where `S` has both `Dict` and `[T]` fields,
to confirm whether the defect is specific to *nested* Dicts-inside-map-values
or any Dict field inside a copied aggregate.

## Workaround (landed)

Module-global registry
`src/compiler/20.hir/hir_lowering/module_registry.spl` (commits
`9f8d5a7a1945` + `797497d757bd`): import resolution refetches modules through
accessor functions instead of reading `HirLowering.modules_by_name` directly.
Plain arg-passing and direct index reads (`ctx.modules[name]`) preserve nested
dicts correctly — only the struct-field copy is corrupted, so routing reads
around that field sidesteps the defect without fixing the underlying
deep-copy bug.

## Related

- `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`
  — "Round 5" section documents the same corruption from the phantom-Some
  symptom side (downstream `.get()`/decode behavior on the nil-filled dicts).
- `doc/08_tracking/bug/bootstrap_lane_dict_global_uninitialized_alloca_2026-07-27.md`
  — sibling defect hit while building the workaround (Dict-typed module
  globals, as opposed to Dict-typed struct fields, also mis-lower in the
  bootstrap lane).
- `src/compiler/20.hir/hir_lowering/module_registry.spl` — workaround
  implementation.
- `src/compiler/20.hir/hir_lowering/types.spl` `hirlowering_for_module` — site
  of the corrupting copy.
