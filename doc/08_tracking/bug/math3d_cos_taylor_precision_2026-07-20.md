# math3d.spl `_cos`/`_sin` Taylor series loses precision away from zero

**Date:** 2026-07-20
**Category:** GENUINE-BUG (numeric precision defect in pure-Simple lib code)
**Spec:** `test/unit/lib/engine/math3d_spec.spl` (24/25 passing — only this example fails)
**Command:** `SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple test test/unit/lib/engine/math3d_spec.spl --no-session-daemon`

## Symptom

`describe "Quaternion" / it "90-degree Y rotation rotates X to Z"` fails.
The other 24 examples in the file pass, including the loose-tolerance
`from_axis_angle creates valid quaternion` test that uses the exact same
`Quaternion.from_axis_angle(axis, angle)` call — so this is not the
static-method-under-`test` landmine
(`generic_class_static_method_unresolved_under_test_2026-07-20.md`); the call
resolves fine, the *numeric result* is off.

## Minimal repro (via `bin/simple run`, values confirmed independently)

```
use std.common.engine.math3d.{Vec3, Quaternion}
use std.common.engine.units.{Angle}
use std.common.math.{MATH_PI}

val axis = Vec3(x: 0.0, y: 1.0, z: 0.0)
val angle = Angle(radians: MATH_PI / 2.0)
val q = Quaternion.from_axis_angle(axis, angle)
val v = Vec3(x: 1.0, y: 0.0, z: 0.0)
val rotated = q.rotate_vector(v)
# spec expects rotated.x ~ 0.0 (tolerance |x*1000| < 1.0)
# actual: rotated.x * 1000.0 = -8.33  (fails the < 1.0 / > -1.0 bound)
# rotated.z * 1000.0 = -999.97 (within the <-999.0 bound, so that half passes)
```

## Root cause

`src/lib/common/engine/math3d.spl`:

```
fn _sin(x: f64) -> f64:
    val pi = 3.141592653589793
    val two_pi = pi * 2.0
    var a = x
    while a > pi: a = a - two_pi
    while a < 0.0 - pi: a = a + two_pi
    val x2 = a * a
    a * (1.0 - x2/6.0 + x2*x2/120.0 - x2*x2*x2/5040.0)   # 4-term Taylor series

fn _cos(x: f64) -> f64:
    _sin(x + 3.141592653589793 / 2.0)
```

`_sin`'s range reduction only folds the angle into `[-pi, pi]`, not into the
`[-pi/2, pi/2]` range where a 4-term Taylor series is accurate. `_cos` calls
`_sin(x + pi/2)`, which for `half = angle.radians/2.0 = pi/4` evaluates
`_sin(3*pi/4) ≈ 2.356 rad` — **outside** the well-converged region. Hand
computing the 4-term series at `a = 3*pi/4`:

```
x2 = a*a = 5.5516
series = 1 - x2/6 + x2^2/120 - x2^3/5040 = 0.297628
_sin(3pi/4) ≈ a * series = 2.35619 * 0.297628 = 0.70127
actual sin(3pi/4) = 0.70710678...
```

That's a ~0.0058 absolute error — small in isolation, but `from_axis_angle`
uses this `_cos(half)` as the quaternion's `w` component directly, and the
error propagates through `rotate_vector`'s cross-product terms into a
visible ~0.008 residual on `rotated.x`, enough to blow the spec's tight
`|x| < 0.001` tolerance for the exact-cardinal-axis case.

The same module's `math2d.spl` has an unrelated but analogous `_sin`/`_cos`
pair (not diagnosed here), and `src/lib/skia/entity/matrix.spl` has its own
independent Taylor implementation with proper `x^15` terms and the same
`[-pi,pi]`-only reduction, which happens not to trip this exact test but has
the same latent risk for angles near `+/-pi`.

## Suggested fix (not applied — src/lib logic change, out of scope for this pass)

Reduce to `[-pi/2, pi/2]` before evaluating the series (quadrant-fold with a
sign/complement adjustment), or add more series terms, or route through the
existing `rt_math_sin`/`rt_math_cos` externs the same way
`src/lib/common/engine/math2d.spl`'s top-level `_sin`/`_cos` wrappers already
do (those call `rt_math_sin`/`rt_math_cos` directly rather than a hand-rolled
Taylor series) — math3d's version reimplements it in pure Taylor form instead
of reusing the extern-backed helper, seemingly to avoid a second extern
declaration; consolidating on the extern-backed version would fix this for
free.
