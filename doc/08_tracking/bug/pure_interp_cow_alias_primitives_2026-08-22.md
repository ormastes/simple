# Pure-Simple core interpreter: every collection write goes through a temp alias

**Date:** 2026-08-22
**Area:** pure-Simple tree-walk interpreter — `src/compiler/10.frontend/core/interpreter/`
(`value.spl`, `eval_access.spl`, `_EvalOps/access_literal_assign_eval.spl`,
`_EvalOps/call_method_eval.spl`)
**Status:** FIXED — pinned by
`test/01_unit/compiler/interpreter/pure_interp_owner_mutation_spec.spl` and five
rows in `scripts/check/check-perf-regression-tests.shs`.
**Class:** the COW-alias class of
`doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md` (seed
fixed 2026-08-21/22), audited on the pure lane so the self-hosted binary does
not carry it.

## What was found

The pure interpreter stores values in parallel arena arrays (`val_arrays`,
`val_struct_fields`, `val_struct_values`, indexed by value id). Every primitive
that WRITES into one of those arrays did it through a temporary alias:

```
var values = val_struct_values[vid]     # copy-on-write share
values[idx] = new_val                   # first write: deep copy of the whole array
val_struct_values[vid] = values         # write the copy back
```

Sites: `value.spl` `val_struct_set_field` / `val_struct_upsert_field` /
`val_struct_set_field_idx` (every `d[k] = v` on an interpreted `__dict` and every
struct field store); `eval_access.spl:311-327` and
`_EvalOps/access_literal_assign_eval.spl:660-663, 738-758` (index assign and
compound index assign); `_EvalOps/call_method_eval.spl:941-943` (array `push`).

Measured under native/JIT value semantics (the mode the self-hosted binary runs
in), 16k pushes into one array: alias form **22,327 ms** (4000 → 8000 → 16000:
1540 / 6498 / 22327 ms, ×4.2 / ×3.4 per doubling = quadratic) vs owner form
`val_arrays[vid].push(x)` **1 ms**, flat. Under the Rust seed's interpreter
(what executes this code today) both forms are quadratic for a different reason
(seed-side nested-global push cost), and `__dict` lookups are a linear name
scan (`val_struct_find_field_idx`), so `val_struct_upsert_field` stays O(n) per
insert (4000 inserts: 37.8 s pre / 43.5 s post, noise on a load-28 box). The
alias term is therefore invisible on the seed and decisive on the self-hosted
binary.

Class 1 of the seed record (`interpreter_me_call_dict_clone_2026-08-22.md`) does
NOT apply to the pure lane: `eval_method_call` pushes the receiver value id
itself (`_EvalOps/call_method_eval.spl:687-694`) and binds it with
`env_define` without any copy gate; `val_copy_if_value_struct` is applied only
to params/returns/let/field-store. MIR lowering likewise excludes `me`/`self`
receivers from `copy_struct_value_recursive`
(`50.mir/_MirLowering/function_lowering.spl:349, 455-470`) and the C runtime
mutates in place with no refcount (`runtime_native.c:8161 rt_dict_set`).

## Fix

Mutate through the single owner at every site:
`val_struct_fields[vid].push(field_name)`, `val_struct_values[vid][idx] = new_val`,
`val_arrays[base_val][idx] = new_val`, `val_arrays[receiver].push(new_elem)`.
`eval_access.spl`'s hand-inlined dict-append now calls
`val_struct_upsert_field`. Semantics verified identical on the seed
(`xs[0].push(9); xs[1][0] = 7` → `3 9 7`) and by the behaviour block of the spec.

## Still open on this lane (filed, not fixed here)

- `__dict` in the pure interpreter is a linear-scan struct; the O(n) lookup
  remains. Routing `__dict` through `interpreter/hashmap.spl` is the real fix
  and is out of scope for a value-semantics-preserving minimal change.
- The pure tree-walk driver cannot currently be executed end to end:
  `scripts/check/class_identity_pure_simple_driver.spl` dies on today's seeds
  with `array index out of bounds: index is 127 but length is 0` (128-bucket env
  hashmap never initialised). This is why the spec pins the mechanism by source
  shape plus a library-level behaviour test rather than by an end-to-end timing.
