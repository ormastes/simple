# CSS timing functions

> Strict parsing and exact CSS Easing evaluation for the bounded scalar timing profile

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

The common timing contract admits one keyword, cubic Bézier, or steps timing
function. It strictly rejects malformed, nonfinite, out-of-range, and list
values. Table-driven examples cover exact step boundaries, the CSS `before`
flag, Bézier y-control evaluation, and endpoint tangent extrapolation.

List-valued timing functions and keyframe-local easing are intentionally
outside this bounded profile.

## Scenarios

- Strictly parse and evaluate the admitted timing table.
- Evaluate Bézier y control points and endpoint tangents.
- Reject malformed, nonfinite, out-of-range, and list values.

<details>
<summary>Exact folded executable SSpec</summary>

The block below is a verbatim mirror of
`test/01_unit/lib/common/animation/timing_spec.spl`.

```simple
# @cover src/lib/common/animation/timing.spl 90%

use std.spec.*
use std.common.animation.timing.{
    parse_timing_function, evaluate_timing, cubic_bezier_at
}

fn expect_near(actual: f64, expected: f64):
    expect((actual - expected).abs()).to_be_less_than(0.00001)

describe "CSS timing functions":
    it "strictly parses and evaluates the admitted timing table":
        val cases: [(text, f64, bool, f64)] = [
            ("linear", 0.5, false, 0.5),
            ("cubic-bezier(0,0,1,1)", 0.5, false, 0.5),
            ("steps(4,jump-start)", 0.0, false, 0.25),
            ("steps(4,jump-start)", 0.25, false, 0.5),
            ("steps(4,jump-start)", 0.25, true, 0.25),
            ("steps(4,jump-end)", 0.249, false, 0.0),
            ("steps(4,jump-end)", 0.25, false, 0.25),
            ("steps(4,jump-none)", 0.25, false, 1.0 / 3.0),
            ("steps(4,jump-both)", 0.0, false, 0.2)
        ]
        for case in cases:
            if val timing = parse_timing_function(case.0):
                expect_near(evaluate_timing(timing, case.1, case.2), case.3)
            else:
                fail("valid timing case did not parse: " + case.0)

    it "evaluates Bézier y control points and endpoint tangents":
        expect_near(
            cubic_bezier_at(0.25, 0.0, 1.0, 1.0, 0.0),
            0.47905547
        )
        expect_near(
            cubic_bezier_at(-0.5, 0.5, 0.25, 0.75, 1.25), -0.25
        )
        expect_near(
            cubic_bezier_at(1.5, 0.5, 0.25, 0.75, 1.25), 0.5
        )

    it "rejects malformed nonfinite out-of-range and list values":
        val invalid = [
            "", "linear()", "cubic-bezier(0,0,1)",
            "cubic-bezier(-0.1,0,1,1)", "cubic-bezier(0,0,1.1,1)",
            "cubic-bezier(0,nan,1,1)", "cubic-bezier(0,inf,1,1)",
            "steps(0,end)", "steps(1,jump-none)", "steps(2,middle)",
            "linear, ease"
        ]
        for value in invalid:
            expect(parse_timing_function(value)).to_be_nil()
```

</details>
