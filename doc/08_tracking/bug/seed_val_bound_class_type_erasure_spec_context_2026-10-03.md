# seed_val_bound_class_type_erasure_spec_context_2026-10-03

Status: open
Date: 2026-10-03
Lane: rendering buffer hardening (skia side), Item 1a

## Symptom

In a spec executed via
`bin/simple test <spec> --mode=interpreter` (Rust seed binary), passing a
`val`-bound class value through a multi-hop free-function chain fails at
runtime with a `semantic: undefined field: ... on Dict` error, e.g.:

- `SkColor4f` bound then passed to `fill_path_aa`
  (`'r' on Dict` at raster_prims.spl `Bitmap.set_pixel`)
- `SkPaint` bound then passed to `sk_picture_op_draw_rrect` and preflighted
  (`'blend_mode' on Dict` in the engine2d bridge preflight scan)

Concretely:

```
val color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)   # or val color = _red()
fill_path_aa(bm, path, color)                            # FAILS ('r' on Dict)
fill_path_aa(bm, path, SkColor4f(r: 1.0, ...))           # PASSES (inline arg)
```

The failing color chain is
`fill_path_aa -> _scan_row -> Bitmap.set_pixel/blend_pixel`
(raster_prims.spl:349/408); `color.r` is only accessed inside the class
method at the end of the chain. A single-hop call (`fill_rect` with a bound
color) works fine, as does a bound value used through a further method call
expression (`bg_paint.with_anti_alias(false)` as the argument).

## Evidence it is a seed test-runner defect, not source/spec

1. The identical program passes under `bin/simple run` (no test runner).
2. Inline argument expressions pass in the SAME spec context; only the
   `val`-bound form fails. Explicit type annotation
   (`val color: SkColor4f = ...`) does not help.
3. No raster_prims source change is involved: reproduced with
   `src/lib/skia/backend/cpu/raster_prims.spl` at HEAD.
4. Minimal repro spec (fails, 1 example):

```
use std.skia.entity.color.{SkColor4f}
use std.skia.entity.path.{sk_path_new}
use std.skia.backend.cpu.raster_prims.{Bitmap, fill_path_aa}
use std.spec.step
describe "repro":
    it "bound color through multi-hop chain":
        var bm = Bitmap.zeros(20, 20)
        val p = sk_path_new().move_to(4.0, 4.0).line_to(16.0, 4.0)
            .line_to(16.0, 16.0).line_to(4.0, 16.0).close()
        val color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
        fill_path_aa(bm, p, color)
        expect(bm.pixels[840] as i64).to_be_greater_than(100)
```

## Workaround applied

- `test/01_unit/lib/skia/raster_prims_spec.spl` ("stroke_path of a line
  segment…") now passes the color inline.
- `test/01_unit/lib/skia/engine2d_bridge_spec.spl` ("rejects rounded
  corners…") now passes the paint inline.

The behaviors under test are unchanged; only the binding form changed.

## Suspected mechanism

The test runner compiles each `it` example as a separate unit; a `val`
binding of class type in the example body is boxed as a generic Dict value
when the callee lives in a module compiled into a different unit, while
inline argument expressions carry their constructor type across the
boundary. Single-hop calls resolve; multi-hop chains (through
`fill_path_aa`'s private `_scan_row`) lose the type. Root-cause belongs in
the seed compiler/test-runner type registration, out of this lane's edit
surface.
