# `rt_dict_values` returns garbage element words for aggregate-keyed dicts (Dict<SymbolId, HirFunction>)

Date: 2026-10-17 (p2_add bootstrap-sanity cycle 138)
Lane: runtime collection accessor (`rt_dict_values`, runtime_native.c:10820)

## Symptom

Every `.values()`-based iteration over `Dict<SymbolId, HirFunction>`
(`module.functions.values()`) yields an array whose element words fault on
first dereference — while guard-first dict-index reads
(`if dict[k] == nil: skip; dict[k].field`) of the SAME dict succeed. The
dict header is healthy (`.len()` reads the live count; `.keys()` works; the
generated codec's keys()+bracket walk works).

Evidence chain (p2_add shim rounds, cycles 91-138):
- mono's `collect_function_entry_v1` (guard-first dict-index) reads the same
  functions dict successfully (mono completes).
- `hir_fn_scalars_at_v1(functions.values(), 0)` (values-array read) faults at
  the first element word (`0xf70620` region, `ldr` on untagged element).
- `fvals_len=5` prints (header live) immediately before the values element
  read faults.
- The module, its dicts, and the whole object graph are promoted by the
  recursive `rt_transient_heap_promote` walker (cycle-137 exonerated arena
  lifetime).

## Compiler-side workaround (landed, cycle 138)

`hir_fn_scalars_at_key_v1` in 20.hir/hir_codec.spl — keys()[position] +
guard-first double access in the codec pool; `prescan_module_functions_v1`
uses it instead of `.values()`.

## Required runtime fix

Audit `rt_dict_values` (runtime_native.c) for the aggregate-key case: the
entries walk pushes `d->entries[i].value`, but for dicts whose keys are
aggregate (struct) values the value words may be stored in a different slot
layout, or the `occupied` scan mis-fires, or the value words are tagged
differently. Minimal repro: build `Dict<SymbolId, HirFunction>` with 5
entries, call `.values()`, dereference element 0. Also audit
`rt_dict_entries` (same walk shape). Until fixed, `.values()` over
aggregate-keyed dicts is forbidden in compiler code (use keys()+guard-first
index — the campaign playbook rule).
