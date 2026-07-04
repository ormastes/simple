# WPT CSS3 Scorecard

> Aggregates CSS3 feature verification results across pure-function tests.

<!-- sdn-diagram:id=wpt_scorecard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wpt_scorecard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wpt_scorecard_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wpt_scorecard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WPT CSS3 Scorecard

Aggregates CSS3 feature verification results across pure-function tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/wpt_scorecard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Aggregates CSS3 feature verification results across pure-function tests.
Render-based WPT tests (selector_color_subset, custom_properties, transforms,
sticky, @supports) require compiled-mode renderer pipeline and are tracked
separately.

Run with: bin/simple test test/feature/web_platform/css/wpt_scorecard_spec.spl

## Scenarios

### WPT CSS3 Scorecard — Pure Function Verification

#### Animations (5/5)

#### interpolate_length midpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(interpolate_length(0.0, 100.0, 0.5), 50.0)).to_equal(true)
```

</details>

#### ease_value linear identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(ease_value(0.5, TimingFunction.Linear), 0.5)).to_equal(true)
```

</details>

#### ease_value ease-in starts slow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ease_value(0.5, TimingFunction.EaseIn) < 0.5).to_equal(true)
```

</details>

#### interpolate Number values

1. CSSValue Number
   - Expected: is_half is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = interpolate(CSSValue.Number(v: 0.0), CSSValue.Number(v: 1.0), 0.5)
val is_half = match result:
    CSSValue.Number(v): approx(v, 0.5)
    _: false
expect(is_half).to_equal(true)
```

</details>

#### interpolate_length boundary values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(approx(interpolate_length(10.0, 20.0, 0.0), 10.0)).to_equal(true)
expect(approx(interpolate_length(10.0, 20.0, 1.0), 20.0)).to_equal(true)
```

</details>

#### Object-Fit (4/4)

#### fill stretches to box

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compute_object_fit(100.0, 50.0, 200.0, 200.0, "fill", "50% 50%")
expect(approx(r.dest_width, 200.0)).to_equal(true)
```

</details>

#### contain preserves aspect ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compute_object_fit(200.0, 100.0, 100.0, 100.0, "contain", "50% 50%")
expect(approx(r.dest_width, 100.0)).to_equal(true)
expect(approx(r.dest_height, 50.0)).to_equal(true)
```

</details>

#### cover fills box

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compute_object_fit(200.0, 100.0, 100.0, 100.0, "cover", "50% 50%")
expect(approx(r.dest_width, 200.0)).to_equal(true)
```

</details>

#### none uses natural dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = compute_object_fit(50.0, 30.0, 100.0, 100.0, "none", "50% 50%")
expect(approx(r.dest_width, 50.0)).to_equal(true)
```

</details>

#### Scrollbar (3/3)

#### track renders on overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
expect(cmds.len() >= 1).to_equal(true)
```

</details>

#### thumb proportional to ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
val thumb = cmd_at(cmds, 1)
expect(thumb.height).to_equal(200)
```

</details>

#### no thumb when content fits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 300.0, 0.0)
expect(cmds.len()).to_equal(1)
```

</details>

#### Transforms (3/3)

#### parse_transform produces functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fns = parse_transform("translate(10px, 20px)")
expect(fns.len()).to_equal(1)
```

</details>

<details>
<summary>Advanced: transforms_to_matrix identity for none</summary>

#### transforms_to_matrix identity for none

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fns = parse_transform("none")
val m = transforms_to_matrix(fns)
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: scale(2) matrix diagonal</summary>

#### scale(2) matrix diagonal

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fns = parse_transform("scale(2)")
val m = transforms_to_matrix(fns)
expect(approx(m.get(0, 0), 2.0)).to_equal(true)
expect(approx(m.get(1, 1), 2.0)).to_equal(true)
```

</details>


</details>

#### @supports (8/8)

#### known property evaluates true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("(display: flex)")).to_equal(true)
```

</details>

#### known property with invalid value evaluates false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("(display: definitely-not-css)")).to_equal(false)
```

</details>

#### unknown property evaluates false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("(nonexistent: value)")).to_equal(false)
```

</details>

#### text-overflow support evaluates true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("(text-overflow: ellipsis)")).to_equal(true)
```

</details>

#### text-overflow invalid keyword evaluates false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("(text-overflow: definitely-not-css)")).to_equal(false)
```

</details>

#### text-transform support evaluates true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("(text-transform: uppercase)")).to_equal(true)
```

</details>

#### supported selector condition evaluates true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("selector(div:has(.badge))")).to_equal(true)
```

</details>

#### unsupported selector pseudo evaluates false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(eval_supports_query("selector(div:popover-open)")).to_equal(false)
```

</details>

#### Custom Properties (2/2)

#### has_var_reference detects var()

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(has_var_reference("color: var(--main)")).to_equal(true)
```

</details>

#### has_var_reference false for plain value

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(has_var_reference("color: red")).to_equal(false)
```

</details>

#### Overall Score

#### WPT CSS3 pure-function score >= 80%

<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = 0
var total = 0

total = total + 1
if approx(interpolate_length(0.0, 100.0, 0.5), 50.0): passed = passed + 1
total = total + 1
if approx(ease_value(0.5, TimingFunction.Linear), 0.5): passed = passed + 1
total = total + 1
if ease_value(0.5, TimingFunction.EaseIn) < 0.5: passed = passed + 1

val ofr = compute_object_fit(100.0, 50.0, 200.0, 200.0, "fill", "50% 50%")
total = total + 1
if approx(ofr.dest_width, 200.0): passed = passed + 1
val ofr2 = compute_object_fit(200.0, 100.0, 100.0, 100.0, "contain", "50% 50%")
total = total + 1
if approx(ofr2.dest_width, 100.0): passed = passed + 1

val sb = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
total = total + 1
if sb.len() >= 1: passed = passed + 1
total = total + 1
if sb.len() == 2: passed = passed + 1

val tfns = parse_transform("scale(2)")
total = total + 1
if tfns.len() == 1: passed = passed + 1
total = total + 1
if eval_supports_query("(display: flex)"): passed = passed + 1
total = total + 1
if not eval_supports_query("(display: definitely-not-css)"): passed = passed + 1
total = total + 1
if eval_supports_query("(text-overflow: ellipsis)"): passed = passed + 1
total = total + 1
if not eval_supports_query("(text-overflow: definitely-not-css)"): passed = passed + 1
total = total + 1
if eval_supports_query("selector(div:has(.badge))"): passed = passed + 1
total = total + 1
if has_var_reference("color: var(--x)"): passed = passed + 1

val score = passed.to_f64() / total.to_f64()
expect(score >= 0.8).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
