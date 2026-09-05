# `std.math.special.sqrt_f64` is not correctly rounded (diverges from `rt_math_sqrt`)

**Status:** OPEN. **Found:** 2026-09-01, by the tranche-2 dual-run pair
`sqrt_f64_vs_rt_math_sqrt` added to
`test/01_unit/lib/common/spec/dual_run_shadow_spec.spl`.

## What is wrong

IEEE-754 **requires** `sqrt` to be correctly rounded: for every input there is
exactly one admissible result, the nearest representable double to the true
square root. `rt_math_sqrt` satisfies this. `std.math.special.sqrt_f64` does
not, and the two therefore disagree in the last bit on inputs whose root is not
exactly representable.

This is not a tolerance question. Unlike `cbrt`, where a last-bit difference is
a legitimate implementation choice and the sibling `cbrt_f64` pair is
deliberately checked with `bit_exact: false`, `sqrt` has a single correct
answer, so a one-ULP difference is a defect in whichever side is wrong — here,
the Simple side.

## Measured divergences

Seed: debug `simple` built from `origin/main` at `c0cae452481`.

| input | `sqrt_f64` (Simple) | `rt_math_sqrt` (oracle) |
|---|---|---|
| `2.0` | `1.414213562373095` | `1.4142135623730951` |
| `1.0e-10` | `0.000009999999999999999` | `0.00001` |
| `2.5` | `1.5811388300841895` | `1.5811388300841898` |

`1.0e-10` is the most legible case: the true root is exactly `1.0e-5`, which
**is** representable, so the Simple result is not merely differently-rounded —
it misses an exactly-representable answer.

Agreement is exact on inputs that are perfect squares of representable values
(`0.0`, `-0.0`, `1.0`, `4.0`, `9.0`, `0.25`, `1.0e10`), which is consistent with
a Newton-Raphson refinement that stops one iteration short of full convergence.

## Why the spec asserts the divergence instead of tolerating it

The pair asserts exact agreement on the 7 exactly-representable inputs, and
asserts that the 3 inputs above **still diverge**, following the sentinel
precedent already set by the `parse_i64` pair in the same spec. Relaxing the
pair to an epsilon comparison would have hidden precisely the drift the
dual-run harness exists to detect.

The sentinel is self-expiring by construction: when `sqrt_f64` is fixed, the
divergence count drops to 0, the assertion fails, and the spec must be updated.
It cannot quietly become a permanent excuse.

## Fix direction (not attempted here)

Add a final Newton-Raphson iteration in the `f64` domain, or round the last
step through the same correctly-rounded primitive the runtime uses. Any fix
must be landed together with the spec update described above.
