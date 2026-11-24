# Interpreter does not link private module globals of a transitively imported module

**Status:** verification-pending
**Date:** 2026-11-23
**Area:** compiler_rust interpreter module dependency linking
**Related:** `interpreter_fd_ownership_private_module_globals_not_linked_2026-08-12.md` (direct-import variant, superseded)

## Reproducer

A spec importing only `compiler.backend_plugin.dynamic_loader.*` and calling
`load_dynamic_backend_plugin_lease(<valid dll>)` fails with:

```text
semantic: ...:54:5: in call to `mutex_lock_gate` (declared at line 176):
variable `_dynlib_lifetime_gate_v1` not found
```

Chain: spec -> `compiler.backend_plugin.dynamic_loader` -> `std.nogc_sync_mut.sffi.dynamic`
-> `std.nogc_sync_mut.sffi.dynlib_lifetime_owner_v1` (private `var _dynlib_lifetime_gate_v1`).
Adding a direct `use std.nogc_sync_mut.sffi.dynlib_lifetime_owner_v1.{dynlib_lifetime_register_v1}`
to the spec makes it pass, so function bodies are linked but module-level
`var` state of the two-hop module is not. Measured on `C:/dev/simple/bin/simple.exe`
(Rust seed, Windows), 2026-11-23.

## Workaround

`test/01_unit/compiler/backend_plugin/dynamic_loader_spec.spl` carries
`@workaround bug=interp_transitive_import_private_globals_not_linked_2026-11-23`.

## Fix status

Fix: module-level initializers evaluate with the importing module's classes merged in
(`init_classes_view` in `src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs`).
Gate: `test/01_unit/compiler/backend_plugin/dynamic_loader_spec.spl` with the `@workaround` removed.
Fail-without: pre-fix seed (`git hash-object` 7502091c / a4b9d2bd), `passed=3 failed=4`, `variable _dynlib_lifetime_gate_v1 not found`.
Pass-with: post-fix seed build, see PR body. Status stays verification-pending until native verification.
