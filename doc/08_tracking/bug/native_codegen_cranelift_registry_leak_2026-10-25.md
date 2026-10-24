# Cranelift bridge keeps every module's handles (2026-10-25)

**Status:** fixed in `src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs`
(test `owned_handle_tests`).

## Root cause

`rt_cranelift_free_module` removed only the module from `AOT_MODULES` /
`JIT_MODULES`. The process-wide maps kept everything else the module had
created:

- `SIGNATURES`: the adapter makes a fresh signature for every runtime-import
  call site and every indirect call;
- `DECLARED_FUNCS` and `DECLARED_DATA`: one handle per declaration;
- `STRING_DATA_CACHE`: a copy of every string constant's bytes, keyed by
  `(module, bytes)`.

All of these lived until the process exited, so a codegen worker grew with
every module it compiled.

## Fix

The bridge now records which module owns each handle:

- function and data handles belong to the module that declared them;
- a signature belongs to the first module that consumes it, through
  `declare_function`, `begin_function` or `call_indirect`;
- `rt_cranelift_free_module` drops everything the module owns, including its
  `STRING_DATA_CACHE` rows;
- a signature consumed by two modules is never released.

The handle counter and emitted objects are unchanged.

## Size

At probe scale (142-module closure) this is small next to
`native_codegen_build_cache_save_retention_2026-10-25.md`. The codegen slope
did not change measurably: 6.7 MB/module before, 6.4 MB/module after.
