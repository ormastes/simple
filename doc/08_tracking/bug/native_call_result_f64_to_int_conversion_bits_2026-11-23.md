# Native/JIT: `f(...).to_i32()` on an f64-returning call converts the raw bit pattern

- **Filed:** 2026-11-23
- **Class:** silent wrong value, seed codegen (native-build with
  `SIMPLE_NATIVE_BUILD_RUST=1`, and `simple run` on the Rust seed)
- **Status:** open. Worked around at the two Engine2D sites that broke corpus
  case 02 on the GB10; the compiler is not fixed.

## Repro

```simple
use std.common.numeric_round.{ceil_f64, floor_f64}

fn local_floor(x: f64) -> f64:
    val t = x as i64 as f64
    if t > x: t - 1.0 else: t

fn main() -> i64:
    val x = 47.26617698462807
    print "A {floor_f64(x).to_i32()} {ceil_f64(240.3).to_i32()}"   # 0 0      (want 47 241)
    val f: f64 = floor_f64(x)
    print "B {f.to_i32()}"                                        # 47
    print "C {floor_f64(x) as i32}"                               # 47
    print "D {local_floor(x).to_i32()}"                           # 0        (want 47)
    print "E {floor_f64(x).to_i64()}"                             # 4631811479262199808 (want 47)
    val g = floor_f64(x)
    print "F {g.to_i32()}"                                        # 47
    0
```

The output is the same from a native-build binary (seed
`~/.cache/cargo-target-wr-gpulink/release/simple`, `--runtime-bundle
host-gpu-native-all`, aarch64 GB10) and from `simple run` on the
webrender-blend seed. `.to_i64()` returns the IEEE-754 bits of 47.0
(`0x4047800000000000`), and `.to_i32()` returns their low 32 bits, which are 0.
A local function shows it too (D), so the defect is not about imports. The
interpreter used by `simple test` returns 47, so an interpreted spec cannot
catch it.

## Trigger

A method-call conversion (`.to_i32()` / `.to_i64()`) whose receiver is a
**call expression** returning `f64`. A receiver bound to a local (typed or
untyped) converts correctly, and so does `as i32`.

## Impact found

`_engine2d_draw_ir_strict_vulkan_affine_pixels` (`draw_ir_adv.spl`) computed
the affine dispatch box as `floor_f64(min_x).to_i32() - 2` etc. Natively that
box became `(0,0,2,2)`, so the rotated tile and the fractional bar of corpus
case 02 were never painted. The GB10 worker then failed with
`Engine2D corpus case 02 edge oracle mismatch` (exact_mismatch=18288,
edge_max=219). The same pattern is in `_engine2d_draw_ir_strict_vulkan_fractional_pixels`.
Both now bind typed f64 locals first. About 20 other `floor_f64/ceil_f64(...).to_iN()`
sites remain in `src/lib` and `src/app`, along with any `<f64 call>.to_iN()`.

## Real fix

The seed lowering of builtin numeric conversions has to use the call
expression's resolved return type (f64 → float-to-int conversion), not an
integer bitcast. Add a native/JIT spec that runs the repro above. Once the
compiler is fixed, remove the workaround comments in `draw_ir_adv.spl`.
