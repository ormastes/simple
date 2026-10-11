# Seed `simple test`: typed fn-valued local is shadowed by a same-named global

**Status:** open. **Found:** 2026-10-04 while removing written `Any` from compiled sources.

## Symptom

```spl
val resolve = svc.module_loader.resolve_fn   # field type: fn(text, text) -> text
val resolved_path = resolve("compiler/driver.spl", "std.math")
```

Under the Rust seed's `simple test`, the call dispatches to the imported global
`std.path.resolve(path, base)` and returns `"std.math/compiler/driver.spl"`
instead of calling the local closure (`_noop_resolve`, which returns
`"std.math"`). The same code is correct under `simple run`.

It was latent while the field was typed `any`: the dynamic call path consulted
the local first. Typing the field as `fn(text, text) -> text` routes the call
through the static-callee path, which prefers the global.

## Reproducer

`test/03_system/compiler/compiler_services_system_spec.spl`, cases
"module loader resolves import paths" and the two later `resolve_fn` cases, with
the local named `resolve`.

## Workaround in tree (recorded, not normalized)

The spec's local is named `resolve_import`. Remove the rename once the seed
resolves a local binding before a same-named imported function.

## Fix direction

Name resolution for a call `f(...)` must check lexical locals (including
fn-typed `val` bindings) before module-level and imported functions, in every
seed execution path that `simple test` uses.
