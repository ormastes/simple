# match pattern binding shadowed by an in-scope module namespace (2026-08-18)

Status: OPEN (compiler defect); call-site unblocked in `engine.spl`.

## Symptom

`test/perf/graphics_2d/backend_probe_spec.spl` — 4 of 6 examples RED:

```
semantic: method `backend_name` not found on type `dict`
  (receiver value: {ADRENO_PREFERRED_WORKGROUP: 64, ..., BACKEND_CPU: cpu, ...})
semantic: method `draw_rect_filled` not found on type `dict` (receiver value: {})
```

`Engine2D.create_with_backend_strict(16, 16, "cpu")` returned `is_ok() == true`
but `.unwrap()` handed back a MODULE NAMESPACE dict, not the `Engine2D`.

## Root cause

A `match` pattern binding whose name equals the last segment of an imported
module path resolves to that module's namespace dict instead of the matched
payload. Minimal reproduction (interpreter lane):

```simple
use std.gpu.engine2d.color.{rgb}
fn f() -> Result<i64, text>: Ok(7)
match f():
    Ok(color):   print "bound={color}"   # prints the color MODULE namespace
match f():
    Ok(v):       print "control={v}"     # prints 7
```

`engine.spl` bound its factory match arms as `Ok(engine)`, colliding with the
in-scope `engine` module namespace.

## Fix applied here (call site only)

`src/lib/gc_async_mut/gpu/engine2d/engine.spl` — renamed the three colliding
match bindings `engine` -> `eng` in `create_with_backend` (two arms) and
`create_with_backend_strict`. Spec back to `6 total, 6 passed, 0 failed`.

## Still open (compiler)

Name resolution must prefer a pattern binding over a module namespace. The fix
lives in the compiler/interpreter scope resolution; it could not be built or
verified in this lane (shared Rust seed, rebuild forbidden).

Unblock condition: rebuild the seed with pattern bindings shadowing module
namespaces, then
`test/01_unit/language/match_binding_module_name_shadow_spec.spl` goes 2/2.

## Specs

- Reproducing: `test/01_unit/gpu/engine2d_strict_create_module_shadow_spec.spl`
  (GREEN after the call-site fix; RED before it).
- Defect class: `test/01_unit/language/match_binding_module_name_shadow_spec.spl`
  — deliberately left RED (1 passed, 1 failed): the passing example is the
  positive control proving the oracle discriminates, the failing one is the
  unfixed compiler defect above.
