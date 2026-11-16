# Phase 2 LLVM: field of an untyped match-bound local lowers to void

- Status: open
- Filed: 2026-11-16
- Module: `compiler.backend.backend_plugin.dynamic_loader`
- Function: `load_dynamic_backend_plugin_lease`

## Symptom

`llc` rejects the emitted IR for module `compiler.backend.backend_plugin.dynamic_loader`:

```
error: void type only allowed for function results
```

The IR contains `dynlib_symbol_address_v1(void %x, ...)`.

## Cause

`var library = match loaded: case Ok(value): value ...` has no declared type, so the
frozen Phase 2 compiler gives the local a void type. Reading `library.handle`
through it then yields a void argument for `dynlib_symbol_address_v1`.

## Workaround

Source-level, in `dynamic_loader.spl`: declare `var library: DynLib = match loaded:` and
pass a typed local `val library_handle: i64 = library.handle` to
`dynlib_symbol_address_v1`. Both sites carry
`# @workaround bug=phase2_llvm_untyped_match_local_field_void_2026-11-16`.

## Resolution

Open. Remove the workaround once the compiler infers the type of a `match` result bound
to an untyped local. No `bug_db.sdn` row is registered for this bug on purpose, to avoid
another seal conflict with other open bug-register PRs.
