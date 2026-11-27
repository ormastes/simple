# Cranelift objects differ between runs of one binary (2026-10-25)

**Status:** observed, not fixed. Found while checking that the fixes in
`mir_fork_child_heap_registry_cow_resize_2026-10-25.md` leave emitted
objects unchanged.

## Observation

The probe was a 142-module closure, built twice with the same binary in
no-fork mode (`SIMPLE_MIR_FORK_WORKERS=0`). Even after canonicalizing each
object, 8 of 119 modules differed between the two runs. Across 7 runs of the
same binary, 10 modules showed more than one digest:

- `elf_parser`
- `decl_attrs`
- `visibility`
- `label`
- `flat_pool_codec`
- `parser_types_expr`
- `hir_symbol_table_methods`
- `hir_types`
- `layout_core`
- `external_text_io`

The differences are real code, not naming. For example,
`compiler.common.diagnostics.label.Label.message` is 284 bytes with 2
`rt_alloc` calls in one run and 700 bytes with 4 in another.

## Canonical form

Canonicalization removes the differences that do not change behaviour:

- `__simple_str_const_<N>` takes `N` from the process-global Cranelift handle
  counter, so it depends on module order. It is renamed by the hash of its
  bytes.
- Section order comes from hash-map iteration, so it is ignored.
- Each defining symbol's section bytes and relocations are compared.

Tool: a scratch `objcanon.py` from the lane that found this. It is not in
the repo.
