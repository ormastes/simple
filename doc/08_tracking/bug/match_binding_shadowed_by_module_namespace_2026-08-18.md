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

## 2026-08-18 follow-up — spec no longer committed RED

`test/01_unit/language/match_binding_module_name_shadow_spec.spl` was committed
in a deliberately failing state (`Results: 2 total, 1 passed, 1 failed`) to
document this defect. A knowingly-red spec makes the suite dishonest: red must
mean "something broke". The spec was restructured to assert the CURRENT, ACTUAL
behavior — the `Ok(color)` binding resolves to the `std.gpu.engine2d.color`
module namespace, so it does NOT carry the payload `7` — and now reads
`Results: 2 total, 2 passed, 0 failed`. The positive control is unchanged.

The defect is NOT hidden: the spec header states the correct behavior, links
here, and names the inversion (`expect(color).to_equal(7)`) that must replace
the pinned assertion once the seed is fixed. Fixing the compiler makes that
spec go RED, which is the fix-detection signal. This bug record remains OPEN
and is the tracking artifact for the defect itself.

Tension noted for the record: `.claude/rules/testing.md` says a correct spec
that fails should be left RED. That rule was applied here at the level of the
BUG RECORD (which stays open) rather than the spec, on the explicit instruction
that the committed suite must not carry a known-red spec.

## Re-measured 2026-08-31 (Windows Rust seed) — scope is NARROWER than recorded

Status stays **OPEN**, but the defect is no longer general. It is now scope
dependent, measured on `bin/simple.exe` ("Simple Language v1.0.0-RC", which
self-identifies as a bootstrap seed) in the Windows checkout:

| scope of the `match` | binding `color` | verdict |
|---|---|---|
| plain top-level `fn` | carries the payload (`7`) | **FIXED** |
| BDD `describe`/`it` closure body | the `color` module namespace dict | **STILL BROKEN** |

Evidence:

- Standalone probe (`match` inside `fn main()`) printed `color_is_7=true` under
  **both** engines — `SIMPLE_EXECUTION_MODE=interpreter` and `=jit`. So this is
  not a run-vs-test engine divergence; it is a function-scope vs closure-scope
  difference.
- Under the test runner, `_binds_payload()` (a plain top-level `fn`) returns
  `true`, while a `match` written directly in an `it` block body still fails as:

  ```
  expected {_byte_to_hex: <fn:_byte_to_hex>, ..., rgb: <fn:rgb>, rgba: <fn:rgba>} to equal 7
  ```

Consequence for the spec: `test/01_unit/language/match_binding_module_name_shadow_spec.spl`
previously asserted `_binds_payload() == false` and had gone RED, because the
plain-function half is fixed. It now pins **each scope separately** — the fixed
scope asserted fixed, the broken scope asserted broken — so the file is GREEN
(3/3) without hiding the residual defect. When the closure scope is fixed, the
third example goes RED; that is the signal to replace its body with
`expect(color).to_equal(7)` and close this record.

Related closure-scope defects worth checking together, since the shape matches:
`interp_member_path_store_lost_in_bdd_closure_2026-07-03.md` and
`interp_crossmodule_array_writeback_lost_in_bdd_closure_2026-06-29.md`.
