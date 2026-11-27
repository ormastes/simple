# BaremetalBackend unit specs execute zero examples — `os.drivers` import does not resolve (2026-11-14)

Status: OPEN. Severity: medium (a whole Simple 2D backend has no executing spec).

## Defect

`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_baremetal_image_clip_spec.spl`
and `test/01_unit/lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl`
import `os.drivers.framebuffer.fb_driver.{FramebufferDriver}`. From a
`test/01_unit/lib` spec the `os` root is not on the module path.

## Repro (seed built 2026-11-14)

```
simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/baremetal_constructor_spec.spl
```

Expected: 6 examples executed.
Actual: `error: SIMPLE_JIT_STRICT: HIR lowering error: cannot resolve import
os.drivers.framebuffer.fb_driver ... module path segment os not found`, then
`error: test-runner: no examples executed`, rc=1. Identical under
`SIMPLE_COVERAGE=1 simple run <spec>`.

## Consequence

`src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl` measures 0 of 337
executable lines (`doc/10_metrics/gpu/render_coverage_2026-11-14.md`).

## Fix direction

Build the framebuffer surface through a `std` path the unit lane can resolve,
or move the two specs to a lane whose module roots include `os`.
