# Matrix4 / ComputedStyle library-path regression guard

> Pins the fix for two `src/lib/` modules that imported from a non-existent

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Matrix4 / ComputedStyle library-path regression guard

Pins the fix for two `src/lib/` modules that imported from a non-existent

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/matrix4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Pins the fix for two `src/lib/` modules that imported from a non-existent
`examples.browser.*` tree. An unresolved `use` is only a WARN in this repo
(exit 0), so the breakage was invisible: `Matrix4.identity()` and
`get_property_from_style` only failed at RUNTIME, and the one spec that called
them was itself already dead from a second broken import.

This spec fails if either import is repointed back at a missing module, because
every example below drives a real value through the library call path rather
than merely importing the symbol.

Run with: bin/simple test test/feature/web_platform/css/matrix4_spec.spl

## Scenarios

### Matrix4 resolves from the library, not from examples/

#### constructors

#### identity has a unit diagonal and zero off-diagonal

- identity has a unit diagonal and zero off-diagonal
   - Expected: approx(m.get(0, 0), 1.0) is true
   - Expected: approx(m.get(1, 1), 1.0) is true
   - Expected: approx(m.get(3, 3), 1.0) is true
   - Expected: approx(m.get(0, 1), 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("identity has a unit diagonal and zero off-diagonal")
val m = Matrix4.identity()
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
expect(approx(m.get(1, 1), 1.0)).to_equal(true)
expect(approx(m.get(3, 3), 1.0)).to_equal(true)
expect(approx(m.get(0, 1), 0.0)).to_equal(true)
```

</details>

#### scale places factors on the diagonal

- scale places factors on the diagonal
   - Expected: approx(m.get(0, 0), 2.0) is true
   - Expected: approx(m.get(1, 1), 3.0) is true
   - Expected: approx(m.get(2, 2), 4.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("scale places factors on the diagonal")
val m = Matrix4.scale(2.0, 3.0, 4.0)
expect(approx(m.get(0, 0), 2.0)).to_equal(true)
expect(approx(m.get(1, 1), 3.0)).to_equal(true)
expect(approx(m.get(2, 2), 4.0)).to_equal(true)
```

</details>

#### translate places offsets in the last column

- translate places offsets in the last column
   - Expected: approx(m.get(0, 3), 10.0) is true
   - Expected: approx(m.get(1, 3), 20.0) is true
   - Expected: approx(m.get(2, 3), 30.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("translate places offsets in the last column")
val m = Matrix4.translate(10.0, 20.0, 30.0)
expect(approx(m.get(0, 3), 10.0)).to_equal(true)
expect(approx(m.get(1, 3), 20.0)).to_equal(true)
expect(approx(m.get(2, 3), 30.0)).to_equal(true)
```

</details>

#### rotate_z(90deg) maps the x axis onto the y axis

- rotate_z(90deg) maps the x axis onto the y axis
   - Expected: approx(m.get(0, 0), 0.0) is true
   - Expected: approx(m.get(1, 0), 1.0) is true
   - Expected: approx(m.get(0, 1), -1.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rotate_z(90deg) maps the x axis onto the y axis")
val m = Matrix4.rotate_z(90.0)
expect(approx(m.get(0, 0), 0.0)).to_equal(true)
expect(approx(m.get(1, 0), 1.0)).to_equal(true)
expect(approx(m.get(0, 1), -1.0)).to_equal(true)
```

</details>

#### get is bounds-checked

- get is bounds-checked
   - Expected: approx(m.get(9, 9), 0.0) is true
   - Expected: approx(m.get(-1, 0), 0.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("get is bounds-checked")
val m = Matrix4.identity()
expect(approx(m.get(9, 9), 0.0)).to_equal(true)
expect(approx(m.get(-1, 0), 0.0)).to_equal(true)
```

</details>

#### multiply

#### identity is a left and right unit

- identity is a left and right unit
   - Expected: approx(left.get(0, 0), 2.0) is true
   - Expected: approx(left.get(1, 1), 5.0) is true
   - Expected: approx(right.get(0, 0), 2.0) is true
   - Expected: approx(right.get(1, 1), 5.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("identity is a left and right unit")
val s = Matrix4.scale(2.0, 5.0, 1.0)
val i = Matrix4.identity()
val left = i.multiply(s)
val right = s.multiply(i)
expect(approx(left.get(0, 0), 2.0)).to_equal(true)
expect(approx(left.get(1, 1), 5.0)).to_equal(true)
expect(approx(right.get(0, 0), 2.0)).to_equal(true)
expect(approx(right.get(1, 1), 5.0)).to_equal(true)
```

</details>

#### composes scale then translate

- composes scale then translate
   - Expected: approx(composed.get(0, 0), 2.0) is true
   - Expected: approx(composed.get(0, 3), 6.0) is true
   - Expected: approx(composed.get(1, 3), 8.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("composes scale then translate")
val composed = Matrix4.scale(2.0, 2.0, 1.0).multiply(Matrix4.translate(3.0, 4.0, 0.0))
expect(approx(composed.get(0, 0), 2.0)).to_equal(true)
expect(approx(composed.get(0, 3), 6.0)).to_equal(true)
expect(approx(composed.get(1, 3), 8.0)).to_equal(true)
```

</details>

#### transform.spl drives Matrix4 through the library import

<details>
<summary>Advanced: transforms_to_matrix('none') is identity</summary>

#### transforms_to_matrix('none') is identity

- transforms_to_matrix('none') is identity
   - Expected: approx(m.get(0, 0), 1.0) is true
   - Expected: approx(m.get(1, 1), 1.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transforms_to_matrix('none') is identity")
val m = transforms_to_matrix(parse_transform("none"))
expect(approx(m.get(0, 0), 1.0)).to_equal(true)
expect(approx(m.get(1, 1), 1.0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: transforms_to_matrix('scale(2)') scales both axes</summary>

#### transforms_to_matrix('scale(2)') scales both axes

- transforms_to_matrix('scale(2)') scales both axes
   - Expected: approx(m.get(0, 0), 2.0) is true
   - Expected: approx(m.get(1, 1), 2.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transforms_to_matrix('scale(2)') scales both axes")
val m = transforms_to_matrix(parse_transform("scale(2)"))
expect(approx(m.get(0, 0), 2.0)).to_equal(true)
expect(approx(m.get(1, 1), 2.0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: transforms_to_matrix('translate(10px, 20px)') offsets</summary>

#### transforms_to_matrix('translate(10px, 20px)') offsets

- transforms_to_matrix('translate(10px, 20px)') offsets
   - Expected: approx(m.get(0, 3), 10.0) is true
   - Expected: approx(m.get(1, 3), 20.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transforms_to_matrix('translate(10px, 20px)') offsets")
val m = transforms_to_matrix(parse_transform("translate(10px, 20px)"))
expect(approx(m.get(0, 3), 10.0)).to_equal(true)
expect(approx(m.get(1, 3), 20.0)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: transforms_to_matrix('rotate(90deg)') rotates</summary>

#### transforms_to_matrix('rotate(90deg)') rotates

- transforms_to_matrix('rotate(90deg)') rotates
   - Expected: approx(m.get(1, 0), 1.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("transforms_to_matrix('rotate(90deg)') rotates")
val m = transforms_to_matrix(parse_transform("rotate(90deg)"))
expect(approx(m.get(1, 0), 1.0)).to_equal(true)
```

</details>


</details>

### ComputedStyle resolves from the library, not from examples/

#### property lookup

#### returns a stored value

- returns a stored value
   - Expected: approx(got, 0.5) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a stored value")
var s = ComputedStyle.empty()
s.set("opacity", CSSValue.Number(v: 0.5))
var got = 0.0
match get_property_from_style(s, "opacity"):
    case CSSValue.Number(v):
        got = v
    case _:
        got = -1.0
expect(approx(got, 0.5)).to_equal(true)
```

</details>

#### returns Unset for an absent property

- returns Unset for an absent property
   - Expected: was_unset is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns Unset for an absent property")
val s = ComputedStyle.empty()
var was_unset = false
match get_property_from_style(s, "width"):
    case CSSValue.Unset:
        was_unset = true
    case _:
        was_unset = false
expect(was_unset).to_equal(true)
```

</details>

#### a later declaration wins

- a later declaration wins
   - Expected: approx(got, 0.75) is true
   - Expected: s.has_property("opacity") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("a later declaration wins")
var s = ComputedStyle.empty()
s.set("opacity", CSSValue.Number(v: 0.25))
s.set("opacity", CSSValue.Number(v: 0.75))
var got = 0.0
match get_property_from_style(s, "opacity"):
    case CSSValue.Number(v):
        got = v
    case _:
        got = -1.0
expect(approx(got, 0.75)).to_equal(true)
expect(s.has_property("opacity")).to_equal(true)
```

</details>

### animation_controller drives ComputedStyle through the library import

#### detect_transitions

#### records a transition when a transitionable property changes

- records a transition when a transitionable property changes
   - Expected: controller.active_transitions.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("records a transition when a transitionable property changes")
val logger = Logger.new("spec", BrowserLogLevel.Error)
val engine = AnimationEngine.new(logger)
var controller = AnimationController.new(engine, logger)

var old_style = ComputedStyle.empty()
old_style.set("width", CSSValue.Length(v: 10.0, unit: "px"))
var new_style = ComputedStyle.empty()
new_style.set("width", CSSValue.Length(v: 50.0, unit: "px"))

controller.detect_transitions(1, old_style, new_style, ["width"], 100.0, "linear")
expect(controller.active_transitions.len()).to_equal(1)
```

</details>

#### records nothing when the property is unchanged

- records nothing when the property is unchanged
   - Expected: controller.active_transitions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("records nothing when the property is unchanged")
val logger = Logger.new("spec", BrowserLogLevel.Error)
val engine = AnimationEngine.new(logger)
var controller = AnimationController.new(engine, logger)

var same = ComputedStyle.empty()
same.set("width", CSSValue.Length(v: 10.0, unit: "px"))

controller.detect_transitions(2, same, same, ["width"], 100.0, "linear")
expect(controller.active_transitions.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c4b7af8db377856f4ef5006e35886cd5228347b6118ab17be9d4c87a62fbd141`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c4b7af8db377856f4ef5006e35886cd5228347b6118ab17be9d4c87a62fbd141`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c4b7af8db377856f4ef5006e35886cd5228347b6118ab17be9d4c87a62fbd141`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/feature/web_platform/css/matrix4_spec.spl
mirror: doc/06_spec/feature/web_platform/css/matrix4_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/matrix4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/matrix4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/matrix4_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/css/matrix4_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identity has a unit diagonal and zero off-diagonal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/matrix4_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scale places factors on the diagonal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/matrix4_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'translate places offsets in the last column' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
