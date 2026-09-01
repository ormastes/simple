# WPT CSS3 Scorecard

> Aggregates CSS3 feature verification results across pure-function tests.

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
| Source | `test/feature/web_platform/css/wpt_scorecard_spec.spl` |
| Updated | 2026-08-26 |
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

- interpolate_length midpoint
- interpolate_length midpoint
   - Expected: approx(interpolate_length(0.0, 100.0, 0.5), 50.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("interpolate_length midpoint")
step("interpolate_length midpoint")
# @req: REQ-FEAT-CSS-WPT-SCORECARD-SPEC-001
expect(approx(interpolate_length(0.0, 100.0, 0.5), 50.0)).to_equal(true)
```

</details>

#### ease_value linear identity

- ease_value linear identity
- ease_value linear identity
   - Expected: approx(ease_value(0.5, TimingFunction.Linear), 0.5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ease_value linear identity")
step("ease_value linear identity")
expect(approx(ease_value(0.5, TimingFunction.Linear), 0.5)).to_equal(true)
```

</details>

#### ease_value ease-in starts slow

- ease_value ease-in starts slow
- ease_value ease-in starts slow
   - Expected: ease_value(0.5, TimingFunction.EaseIn) < 0.5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ease_value ease-in starts slow")
step("ease_value ease-in starts slow")
expect(ease_value(0.5, TimingFunction.EaseIn) < 0.5).to_equal(true)
```

</details>

#### interpolate Number values

- interpolate Number values
- interpolate Number values
   - Expected: is_half is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("interpolate Number values")
step("interpolate Number values")
val result = interpolate(CSSValue.Number(v: 0.0), CSSValue.Number(v: 1.0), 0.5)
val is_half = match result:
    CSSValue.Number(v): approx(v, 0.5)
    _: false
expect(is_half).to_equal(true)
```

</details>

#### interpolate_length boundary values

- interpolate_length boundary values
- interpolate_length boundary values
   - Expected: approx(interpolate_length(10.0, 20.0, 0.0), 10.0) is true
   - Expected: approx(interpolate_length(10.0, 20.0, 1.0), 20.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("interpolate_length boundary values")
step("interpolate_length boundary values")
expect(approx(interpolate_length(10.0, 20.0, 0.0), 10.0)).to_equal(true)
expect(approx(interpolate_length(10.0, 20.0, 1.0), 20.0)).to_equal(true)
```

</details>

#### Object-Fit (4/4)

#### fill stretches to box

- fill stretches to box
- fill stretches to box
   - Expected: approx(r.dest_width, 200.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("fill stretches to box")
step("fill stretches to box")
val r = compute_object_fit(100.0, 50.0, 200.0, 200.0, "fill", "50% 50%")
expect(approx(r.dest_width, 200.0)).to_equal(true)
```

</details>

#### contain preserves aspect ratio

- contain preserves aspect ratio
- contain preserves aspect ratio
   - Expected: approx(r.dest_width, 100.0) is true
   - Expected: approx(r.dest_height, 50.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("contain preserves aspect ratio")
step("contain preserves aspect ratio")
val r = compute_object_fit(200.0, 100.0, 100.0, 100.0, "contain", "50% 50%")
expect(approx(r.dest_width, 100.0)).to_equal(true)
expect(approx(r.dest_height, 50.0)).to_equal(true)
```

</details>

#### cover fills box

- cover fills box
- cover fills box
   - Expected: approx(r.dest_width, 200.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("cover fills box")
step("cover fills box")
val r = compute_object_fit(200.0, 100.0, 100.0, 100.0, "cover", "50% 50%")
expect(approx(r.dest_width, 200.0)).to_equal(true)
```

</details>

#### none uses natural dimensions

- none uses natural dimensions
- none uses natural dimensions
   - Expected: approx(r.dest_width, 50.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("none uses natural dimensions")
step("none uses natural dimensions")
val r = compute_object_fit(50.0, 30.0, 100.0, 100.0, "none", "50% 50%")
expect(approx(r.dest_width, 50.0)).to_equal(true)
```

</details>

#### Scrollbar (3/3)

#### track renders on overflow

- track renders on overflow
- track renders on overflow
   - Expected: cmds.len() >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("track renders on overflow")
step("track renders on overflow")
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
expect(cmds.len() >= 1).to_equal(true)
```

</details>

#### thumb proportional to ratio

- thumb proportional to ratio
- thumb proportional to ratio
   - Expected: thumb.height equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("thumb proportional to ratio")
step("thumb proportional to ratio")
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
val thumb = cmd_at(cmds, 1)
expect(thumb.height).to_equal(200)
```

</details>

#### no thumb when content fits

- no thumb when content fits
- no thumb when content fits
   - Expected: cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("no thumb when content fits")
step("no thumb when content fits")
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 300.0, 0.0)
expect(cmds.len()).to_equal(1)
```

</details>

#### Transforms (3/3)

#### parse_transform produces functions

- parse_transform produces functions
- parse_transform produces functions
   - Expected: fns.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parse_transform produces functions")
step("parse_transform produces functions")
val fns = parse_transform("translate(10px, 20px)")
expect(fns.len()).to_equal(1)
```

</details>

<details>
<summary>Advanced: transforms_to_matrix identity for none</summary>

#### transforms_to_matrix identity for none

- transforms_to_matrix identity for none
- transforms_to_matrix identity for none
   - Expected: approx(m.get(0, 0), 1.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transforms_to_matrix identity for none")
step("transforms_to_matrix identity for none")
val fns = parse_transform("none")
val m = transforms_to_matrix(fns)
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: scale(2) matrix diagonal</summary>

#### scale(2) matrix diagonal

- scale(2) matrix diagonal
- scale(2) matrix diagonal
   - Expected: approx(m.get(0, 0), 2.0) is true
   - Expected: approx(m.get(1, 1), 2.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("scale(2) matrix diagonal")
step("scale(2) matrix diagonal")
val fns = parse_transform("scale(2)")
val m = transforms_to_matrix(fns)
expect(approx(m.get(0, 0), 2.0)).to_equal(true)
expect(approx(m.get(1, 1), 2.0)).to_equal(true)
```

</details>


</details>

#### @supports (8/8)

#### known property evaluates true

- known property evaluates true
- known property evaluates true
   - Expected: eval_supports_query("(display: flex)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("known property evaluates true")
step("known property evaluates true")
expect(eval_supports_query("(display: flex)")).to_equal(true)
```

</details>

#### known property with invalid value evaluates false

- known property with invalid value evaluates false
- known property with invalid value evaluates false
   - Expected: eval_supports_query("(display: definitely-not-css)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("known property with invalid value evaluates false")
step("known property with invalid value evaluates false")
expect(eval_supports_query("(display: definitely-not-css)")).to_equal(false)
```

</details>

#### unknown property evaluates false

- unknown property evaluates false
- unknown property evaluates false
   - Expected: eval_supports_query("(nonexistent: value)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unknown property evaluates false")
step("unknown property evaluates false")
expect(eval_supports_query("(nonexistent: value)")).to_equal(false)
```

</details>

#### text-overflow support evaluates true

- text-overflow support evaluates true
- text-overflow support evaluates true
   - Expected: eval_supports_query("(text-overflow: ellipsis)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("text-overflow support evaluates true")
step("text-overflow support evaluates true")
expect(eval_supports_query("(text-overflow: ellipsis)")).to_equal(true)
```

</details>

#### text-overflow invalid keyword evaluates false

- text-overflow invalid keyword evaluates false
- text-overflow invalid keyword evaluates false
   - Expected: eval_supports_query("(text-overflow: definitely-not-css)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("text-overflow invalid keyword evaluates false")
step("text-overflow invalid keyword evaluates false")
expect(eval_supports_query("(text-overflow: definitely-not-css)")).to_equal(false)
```

</details>

#### text-transform support evaluates true

- text-transform support evaluates true
- text-transform support evaluates true
   - Expected: eval_supports_query("(text-transform: uppercase)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("text-transform support evaluates true")
step("text-transform support evaluates true")
expect(eval_supports_query("(text-transform: uppercase)")).to_equal(true)
```

</details>

#### supported selector condition evaluates true

- supported selector condition evaluates true
- supported selector condition evaluates true
   - Expected: eval_supports_query("selector(div:has(.badge))") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supported selector condition evaluates true")
step("supported selector condition evaluates true")
expect(eval_supports_query("selector(div:has(.badge))")).to_equal(true)
```

</details>

#### unsupported selector pseudo evaluates false

- unsupported selector pseudo evaluates false
- unsupported selector pseudo evaluates false
   - Expected: eval_supports_query("selector(div:popover-open)") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("unsupported selector pseudo evaluates false")
step("unsupported selector pseudo evaluates false")
expect(eval_supports_query("selector(div:popover-open)")).to_equal(false)
```

</details>

#### Custom Properties (2/2)

#### has_var_reference detects var()

- has_var_reference detects var()
- has_var_reference detects var()
   - Expected: has_var_reference("color: var(--main)") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has_var_reference detects var()")
step("has_var_reference detects var()")
expect(has_var_reference("color: var(--main)")).to_equal(true)
```

</details>

#### has_var_reference false for plain value

- has_var_reference false for plain value
- has_var_reference false for plain value
   - Expected: has_var_reference("color: red") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has_var_reference false for plain value")
step("has_var_reference false for plain value")
expect(has_var_reference("color: red")).to_equal(false)
```

</details>

#### Overall Score

#### WPT CSS3 pure-function score >= 80%

- WPT CSS3 pure-function score >= 80%
- WPT CSS3 pure-function score >= 80%
   - Expected: score >= 0.8 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("WPT CSS3 pure-function score >= 80%")
step("WPT CSS3 pure-function score >= 80%")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-CSS-WPT-SCORECARD-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `91ece8b52123ed08f8601350fea9fd248336de66843bb2b048fd5cb339be097a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `91ece8b52123ed08f8601350fea9fd248336de66843bb2b048fd5cb339be097a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `91ece8b52123ed08f8601350fea9fd248336de66843bb2b048fd5cb339be097a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/web_platform/css/wpt_scorecard_spec.spl
mirror: doc/06_spec/feature/web_platform/css/wpt_scorecard_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/wpt_scorecard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/wpt_scorecard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/wpt_scorecard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/css/wpt_scorecard_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interpolate_length midpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/wpt_scorecard_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ease_value linear identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/wpt_scorecard_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ease_value ease-in starts slow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
