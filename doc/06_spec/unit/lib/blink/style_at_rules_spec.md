# Blink At-Rule Specification

> `@media`, `@supports` and `@keyframes` parse in `css_parser` and are decided here, against a media environment and against a registry of what blink's cascade actually implements. Two behaviours matter more than the happy path: a non-matching block contributes nothing, and a block whose prelude cannot be evaluated contributes nothing AND is reported — never silently applied.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Blink At-Rule Specification

`@media`, `@supports` and `@keyframes` parse in `css_parser` and are decided here, against a media environment and against a registry of what blink's cascade actually implements. Two behaviours matter more than the happy path: a non-matching block contributes nothing, and a block whose prelude cannot be evaluated contributes nothing AND is reported — never silently applied.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Browser / Blink |
| Status | Active |
| Source | `test/unit/lib/blink/style_at_rules_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`@media`, `@supports` and `@keyframes` parse in `css_parser` and are decided
here, against a media environment and against a registry of what blink's
cascade actually implements. Two behaviours matter more than the happy path:
a non-matching block contributes nothing, and a block whose prelude cannot be
evaluated contributes nothing AND is reported — never silently applied.

Document order is also pinned: a matching block's rules are spliced back where
the author wrote them, because same-specificity ties are broken by order and
appending them at the end would change which rule wins.

## Scenarios

### at-rule parsing

#### keeps a media block's rules out of the top-level rule list

- keeps a media block's rules out of the top-level rule list
- parse a sheet with one plain rule and one inside @media
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.at_rules.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a media block's rules out of the top-level rule list")
step("parse a sheet with one plain rule and one inside @media")
val sheet = _sheet("p { color: red; } @media print { p { color: blue; } }")
expect(sheet.rules.len()).to_equal(1)
expect(sheet.at_rules.len()).to_equal(1)
```

</details>

#### records the prelude verbatim for later evaluation

- records the prelude verbatim for later evaluation
- parse `@media screen and (min-width: 600px)`
   - Expected: prelude equals `screen and (min-width: 600px)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records the prelude verbatim for later evaluation")
step("parse `@media screen and (min-width: 600px)`")
val sheet = _sheet("@media screen and (min-width: 600px) { p { color: red; } }")
val prelude = sheet.at_rules[0 as i32].prelude
expect(prelude).to_equal("screen and (min-width: 600px)")
```

</details>

#### records a statement at-rule that has no block

- records a statement at-rule that has no block
- parse `@import url(a.css);`
   - Expected: sheet.at_rules.len() equals `1`
   - Expected: sheet.at_rules[0 as i32].name equals `import`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records a statement at-rule that has no block")
step("parse `@import url(a.css);`")
val sheet = _sheet("@import url(a.css); p { color: red; }")
expect(sheet.at_rules.len()).to_equal(1)
expect(sheet.at_rules[0 as i32].name).to_equal("import")
```

</details>

#### skips an at-rule block it does not model instead of reading it as a style rule

- skips an at-rule block it does not model instead of reading it as a style rule
- parse `@font-face { font-family: X; }` followed by a real rule
   - Expected: sheet.rules.len() equals `1`
   - Expected: sheet.rules[0 as i32].selector equals `p`
   - Expected: sheet.errors.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips an at-rule block it does not model instead of reading it as a style rule")
step("parse `@font-face { font-family: X; }` followed by a real rule")
val sheet = _sheet("@font-face { font-family: X; } p { color: red; }")
expect(sheet.rules.len()).to_equal(1)
expect(sheet.rules[0 as i32].selector).to_equal("p")
expect(sheet.errors.len() > 0).to_equal(true)
```

</details>

#### parses a keyframes block into one keyframe per selector

- parses a keyframes block into one keyframe per selector
- parse `@keyframes fade` with from, 50% and to
   - Expected: sheet.keyframes.len() equals `1`
   - Expected: sheet.keyframes[0 as i32].name equals `fade`
   - Expected: sheet.keyframes[0 as i32].keyframes.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a keyframes block into one keyframe per selector")
step("parse `@keyframes fade` with from, 50% and to")
val sheet = _sheet(
    "@keyframes fade { from { opacity: 0; } 50% { opacity: 0.5; } to { opacity: 1; } }")
expect(sheet.keyframes.len()).to_equal(1)
expect(sheet.keyframes[0 as i32].name).to_equal("fade")
expect(sheet.keyframes[0 as i32].keyframes.len()).to_equal(3)
```

</details>

#### splits a keyframe selector list into one keyframe each

- splits a keyframe selector list into one keyframe each
- parse `0%, 100% { opacity: 1; }` as a single entry with two selectors
   - Expected: sheet.keyframes[0 as i32].keyframes.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits a keyframe selector list into one keyframe each")
step("parse `0%, 100% { opacity: 1; }` as a single entry with two selectors")
val sheet = _sheet("@keyframes blink { 0%, 100% { opacity: 1; } }")
expect(sheet.keyframes[0 as i32].keyframes.len()).to_equal(2)
```

</details>

### flattening a media block

#### applies a media block whose query matches the viewport

- applies a media block whose query matches the viewport
- flatten `@media (min-width: 600px)` at 1200px wide


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies a media block whose query matches the viewport")
step("flatten `@media (min-width: 600px)` at 1200px wide")
expect(_flat("@media (min-width: 600px) { p { color: red; } }", 1200.0, 800.0)).to_equal(
    "p{color=red}")
```

</details>

#### drops a media block whose query does not match

- drops a media block whose query does not match
- flatten the same sheet at 320px wide
   - Expected: _flat("@media (min-width: 600px) { p { color: red; } }", 320.0, 640.0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops a media block whose query does not match")
step("flatten the same sheet at 320px wide")
expect(_flat("@media (min-width: 600px) { p { color: red; } }", 320.0, 640.0)).to_equal("")
```

</details>

#### drops a print block when rendering to a screen

- drops a print block when rendering to a screen
- flatten `@media print`
   - Expected: _flat("@media print { p { color: blue; } }", 1200.0, 800.0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops a print block when rendering to a screen")
step("flatten `@media print`")
expect(_flat("@media print { p { color: blue; } }", 1200.0, 800.0)).to_equal("")
```

</details>

#### splices a matching block back into the position the author wrote it

- splices a matching block back into the position the author wrote it
- flatten a sheet where the media block sits BETWEEN two plain rules


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splices a matching block back into the position the author wrote it")
step("flatten a sheet where the media block sits BETWEEN two plain rules")
val source = "a { color: red; } @media (min-width: 600px) { b { color: green; } } c { color: blue; }"
expect(_flat(source, 1200.0, 800.0)).to_equal(
    "a{color=red}|b{color=green}|c{color=blue}")
```

</details>

#### leaves the surrounding rules adjacent when the block does not match

- leaves the surrounding rules adjacent when the block does not match
- flatten the same sheet at a width the query rejects
   - Expected: _flat(source, 320.0, 640.0) equals `a{color=red}|c{color=blue}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves the surrounding rules adjacent when the block does not match")
step("flatten the same sheet at a width the query rejects")
val source = "a { color: red; } @media (min-width: 600px) { b { color: green; } } c { color: blue; }"
expect(_flat(source, 320.0, 640.0)).to_equal("a{color=red}|c{color=blue}")
```

</details>

### flattening a supports block

#### applies a supports block for a property and value blink implements

- applies a supports block for a property and value blink implements
- flatten `@supports (display: flex)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies a supports block for a property and value blink implements")
step("flatten `@supports (display: flex)`")
expect(_flat("@supports (display: flex) { p { color: red; } }", 1200.0, 800.0)).to_equal(
    "p{color=red}")
```

</details>

#### drops a supports block for a value blink does not implement

- drops a supports block for a value blink does not implement
- flatten `@supports (display: grid)` — blink's cascade has no grid
   - Expected: _flat("@supports (display: grid) { p { color: red; } }", 1200.0, 800.0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("drops a supports block for a value blink does not implement")
step("flatten `@supports (display: grid)` — blink's cascade has no grid")
expect(_flat("@supports (display: grid) { p { color: red; } }", 1200.0, 800.0)).to_equal("")
```

</details>

#### applies the author's fallback branch guarded by not

- applies the author's fallback branch guarded by not
- flatten `@supports not (display: grid)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies the author's fallback branch guarded by not")
step("flatten `@supports not (display: grid)`")
expect(_flat("@supports not (display: grid) { p { color: red; } }", 1200.0, 800.0)).to_equal(
    "p{color=red}")
```

</details>

#### declares support for a real subset, not for everything

- declares support for a real subset, not for everything
- check the registry is populated but finite
   - Expected: bounded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares support for a real subset, not for everything")
step("check the registry is populated but finite")
val features = blink_supports_registry().features
val bounded = features.len() > 0 and features.len() < 200
expect(bounded).to_equal(true)
```

</details>

### unevaluatable preludes

#### does not apply a block whose media feature it cannot evaluate

- does not apply a block whose media feature it cannot evaluate
- flatten `@media (hover: hover)`
   - Expected: _flat("@media (hover: hover) { p { color: red; } }", 1200.0, 800.0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not apply a block whose media feature it cannot evaluate")
step("flatten `@media (hover: hover)`")
expect(_flat("@media (hover: hover) { p { color: red; } }", 1200.0, 800.0)).to_equal("")
```

</details>

#### lists the unevaluated prelude instead of dropping it silently

- lists the unevaluated prelude instead of dropping it silently
- count the unevaluated preludes of the same sheet
   - Expected: _unevaluated_count("@media (hover: hover) { p { color: red; } }") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists the unevaluated prelude instead of dropping it silently")
step("count the unevaluated preludes of the same sheet")
expect(_unevaluated_count("@media (hover: hover) { p { color: red; } }")).to_equal(1)
```

</details>

#### lists an unevaluated supports prelude

- lists an unevaluated supports prelude
- flatten `@supports selector(a > b)`
   - Expected: _unevaluated_count("@supports selector(a > b) { p { color: red; } }") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists an unevaluated supports prelude")
step("flatten `@supports selector(a > b)`")
expect(_unevaluated_count("@supports selector(a > b) { p { color: red; } }")).to_equal(1)
```

</details>

#### reports nothing unevaluated for a sheet it fully understands

- reports nothing unevaluated for a sheet it fully understands
- flatten a sheet of plain rules and an evaluable media block
   - Expected: _unevaluated_count("p { color: red; } @media print { p { color: blue; } }") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports nothing unevaluated for a sheet it fully understands")
step("flatten a sheet of plain rules and an evaluable media block")
expect(_unevaluated_count("p { color: red; } @media print { p { color: blue; } }")).to_equal(0)
```

</details>

#### answers an at-rule it does not model as unevaluated rather than as applicable

- answers an at-rule it does not model as unevaluated rather than as applicable
- evaluate an @import at-rule directly
   - Expected: verdict equals `unevaluated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers an at-rule it does not model as unevaluated rather than as applicable")
step("evaluate an @import at-rule directly")
val sheet = _sheet("@import url(a.css);")
var verdict: text = "unevaluated"
if val v = evaluate_at_rule(sheet.at_rules[0 as i32],
        media_environment_screen(1200.0, 800.0), blink_supports_registry()):
    if v:
        verdict = "apply"
    else:
        verdict = "skip"
expect(verdict).to_equal("unevaluated")
```

</details>

#### does not hoist a nested at-rule out of its outer condition

- does not hoist a nested at-rule out of its outer condition
- flatten a `@media print` containing a nested `@media (min-width: 1px)`
   - Expected: _flat(source, 1200.0, 800.0) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not hoist a nested at-rule out of its outer condition")
step("flatten a `@media print` containing a nested `@media (min-width: 1px)`")
val source = "@media print { @media (min-width: 1px) { p { color: red; } } }"
expect(_flat(source, 1200.0, 800.0)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `27bb0f638807bb63343e07b50141ed52a48f1f4aabd9d0d96d3bbe6777b1816e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `27bb0f638807bb63343e07b50141ed52a48f1f4aabd9d0d96d3bbe6777b1816e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `27bb0f638807bb63343e07b50141ed52a48f1f4aabd9d0d96d3bbe6777b1816e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/lib/blink/style_at_rules_spec.spl
mirror: doc/06_spec/unit/lib/blink/style_at_rules_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/blink/style_at_rules_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/blink/style_at_rules_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/blink/style_at_rules_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/blink/style_at_rules_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a media block's rules out of the top-level rule list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/style_at_rules_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records the prelude verbatim for later evaluation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/blink/style_at_rules_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records a statement at-rule that has no block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
