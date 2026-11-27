# Seed `simple test`: typed fn-valued local is shadowed by a same-named global

**Status:** FIXED 2026-11-06 (branch `work/seed-interp-batch2-20261106`) — see "Resolution". **Found:** 2026-10-04 while removing written `Any` from compiled sources.

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

## Resolution (2026-11-06)

`interpreter_call/mod.rs` `evaluate_call`: a new Priority 3.9 calls a
LEXICAL local (`Env::is_local` — frame or block binding) whose value is a
`Value::Function`/`Value::Lambda` before Priority 4. Priority 4's explicit
import binding (`import_bound_candidate`, added 2026-08-31) and the
overload selection used to run first, so the imported `std.path.resolve`
won over the local. Module-level functions mirrored into the env are not
locals and keep the overload/import selection.

The workaround is removed: the spec's local is named `resolve` again.

Evidence (seed built from `release/1.0.0` @ `ecb705896a4` vs this branch,
`simple test`):
- `test/03_system/compiler/compiler_services_system_spec.spl` with the local
  renamed back: base `26 passed, 3 failed` (`expected
  std.math/compiler/driver.spl to equal std.math`, ...); fixed 29/29.
- `test/fixtures/seed_interp/typed_fn_local_shadows_global_test_lane_repro.spl`:
  base 0/1 (same message), fixed 1/1.
- Rust test
  `interpreter_call::local_callable_shadows_import_tests::fn_valued_local_wins_over_an_import_bound_function`:
  FAILED before (`left: 703, right: 3`), ok after.
