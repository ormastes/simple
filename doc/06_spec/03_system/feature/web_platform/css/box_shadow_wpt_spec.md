# CSS Box Shadow Rendering

> Proves admitted outer, multi-outer, and single-inset box shadows through the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Box Shadow Rendering

Proves admitted outer, multi-outer, and single-inset box shadows through the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves admitted outer, multi-outer, and single-inset box shadows through the
existing web semantic/layout owner, Draw IR metadata, and Engine2D pixels.
Mixed inset/outer stacks, multiple inset layers, and full filter-equivalent
blur remain outside this bounded profile.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS box-shadow lowering

#### should paint an offset outer shadow behind the border box

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-003/004
```

</details>

#### should preserve blur and spread length order

- should preserve blur and spread length order
   - Artifact capture: after_step
- Resolve blur and spread boxes in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read exact blur and spread coverage pixels through Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve blur and spread length order")
val blur_shadow = "0px 0px 2px #dc2626"
val spread_shadow = "0px 0px 0px 2px #2563eb"
val blur_html = _shadow_html(blur_shadow, "#111827")
val spread_html = _shadow_html(spread_shadow, "#111827")

step("Resolve blur and spread boxes in canonical web semantic and layout state")
_expect_web_layout(blur_html)
_expect_web_layout(spread_html)

step("Render HTML and CSS through canonical Draw IR")
val blur_composition = _shadow_composition(blur_html)
val spread_composition = _shadow_composition(spread_html)
val blur_panel = _draw_ir_panel(
    blur_composition, blur_shadow, "1"
)
val spread_panel = _draw_ir_panel(
    spread_composition, spread_shadow, "1"
)
expect(_style_value(
    blur_panel, "box-shadow-blur-radius"
)).to_equal("2")
expect(_style_value(
    spread_panel, "box-shadow-blur-radius"
)).to_equal("0")

step("Read exact blur and spread coverage pixels through Engine2D")
expect(_pixels(
    blur_html, blur_composition
)[9 + WIDTH]).to_equal(0xFFDC2626u32)
expect(_pixels(
    spread_html, spread_composition
)[9 + WIDTH]).to_equal(0xFF2563EBu32)
```

</details>

#### should resolve admitted shadow color syntaxes before Draw IR

- should resolve admitted shadow color syntaxes before Draw IR
   - Artifact capture: after_step
- Resolve color-bearing boxes in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read exact resolved shadow colors through Engine2D
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve admitted shadow color syntaxes before Draw IR")
val rgb_shadow = "0px 0px 0px 2px rgb(37, 99, 235)"
val rgba_shadow = "0px 0px 0px 2px rgba(37, 99, 235, 0.5)"
val named_shadow = "0px 0px 0px 2px rebeccapurple"
val hsl_shadow = "0px 0px 0px 2px hsl(120, 100%, 50%)"
val current_shadow = "0px 0px 0px 2px currentColor"
val rgb_html = _shadow_html(rgb_shadow, "#111827")
val rgba_html = _shadow_html(rgba_shadow, "#111827")
val named_html = _shadow_html(named_shadow, "#111827")
val hsl_html = _shadow_html(hsl_shadow, "#111827")
val current_html = _shadow_html(current_shadow, "#db2777")

step("Resolve color-bearing boxes in canonical web semantic and layout state")
_expect_web_layout(rgb_html)
_expect_web_layout(rgba_html)
_expect_web_layout(named_html)
_expect_web_layout(hsl_html)
_expect_web_layout(current_html)

step("Render HTML and CSS through canonical Draw IR")
val rgb_composition = _shadow_composition(rgb_html)
val rgba_composition = _shadow_composition(rgba_html)
val named_composition = _shadow_composition(named_html)
val hsl_composition = _shadow_composition(hsl_html)
val current_composition = _shadow_composition(current_html)
_draw_ir_panel(rgb_composition, rgb_shadow, "1")
_draw_ir_panel(rgba_composition, rgba_shadow, "1")
_draw_ir_panel(named_composition, named_shadow, "1")
_draw_ir_panel(hsl_composition, hsl_shadow, "1")
_draw_ir_panel(current_composition, current_shadow, "1")

step("Read exact resolved shadow colors through Engine2D")
expect(_pixels(
    rgb_html, rgb_composition
)[9 + WIDTH]).to_equal(0xFF2563EBu32)
expect(_pixels(
    rgba_html, rgba_composition
)[9 + WIDTH]).to_equal(0xFF92B1F5u32)
expect(_pixels(
    named_html, named_composition
)[9 + WIDTH]).to_equal(0xFF663399u32)
expect(_pixels(
    hsl_html, hsl_composition
)[9 + WIDTH]).to_equal(0xFF00FF00u32)
expect(_pixels(
    current_html, current_composition
)[9 + WIDTH]).to_equal(0xFFDB2777u32)
```

</details>

#### should paint both admitted outer shadow layers

- should paint both admitted outer shadow layers
   - Artifact capture: after_step
- Resolve the layered shadow box in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read one exact pixel from each shadow layer through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: pixels[10 + WIDTH] equals `0xFFDC2626u32`
   - Expected: pixels[1 + 8 * WIDTH] equals `0xFF2563EBu32`
   - Expected: pixels[2 + 2 * WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should paint both admitted outer shadow layers")
val shadow = (
    "4px 0px 0px #dc2626, 0px 4px 0px #2563eb"
)
val html = _shadow_html(shadow, "#111827")

step("Resolve the layered shadow box in canonical web semantic and layout state")
_expect_web_layout(html)

step("Render HTML and CSS through canonical Draw IR")
val composition = _shadow_composition(html)
_draw_ir_panel(composition, shadow, "2")

step("Read one exact pixel from each shadow layer through Engine2D")
val pixels = _pixels(html, composition)
expect(pixels[10 + WIDTH]).to_equal(0xFFDC2626u32)
expect(pixels[1 + 8 * WIDTH]).to_equal(0xFF2563EBu32)
expect(pixels[2 + 2 * WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

#### should paint a single inset shadow before the center fill

- should paint a single inset shadow before the center fill
   - Artifact capture: after_step
- Resolve the inset shadow box in canonical web semantic and layout state
   - Artifact capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Artifact capture: after_step
- Read exact inset-edge and center pixels through Engine2D
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: pixels[1] equals `0xFF16A34Au32`
   - Expected: pixels[4 + 3 * WIDTH] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should paint a single inset shadow before the center fill")
val shadow = "inset 0px 0px 0px 2px #16a34a"
val html = _shadow_html(shadow, "#111827")

step("Resolve the inset shadow box in canonical web semantic and layout state")
_expect_web_layout(html)

step("Render HTML and CSS through canonical Draw IR")
val composition = _shadow_composition(html)
_draw_ir_panel(composition, shadow, "1")

step("Read exact inset-edge and center pixels through Engine2D")
val pixels = _pixels(html, composition)
expect(pixels[1]).to_equal(0xFF16A34Au32)
expect(pixels[4 + 3 * WIDTH]).to_equal(0xFFFFFFFFu32)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003/004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c5d9bfad0f69065183ef90cdd7fc9c24f5dbedbbd48a4366528c11866352829`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c5d9bfad0f69065183ef90cdd7fc9c24f5dbedbbd48a4366528c11866352829`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c5d9bfad0f69065183ef90cdd7fc9c24f5dbedbbd48a4366528c11866352829`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/box_shadow_wpt_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=65 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/box_shadow_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/box_shadow_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:115:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should paint an offset outer shadow behind the border box' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should paint an offset outer shadow behind the border box' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:139:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve blur and spread length order' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve blur and spread length order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:178:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve admitted shadow color syntaxes before Draw IR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve admitted shadow color syntaxes before Draw IR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:231:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should paint both admitted outer shadow layers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:231:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should paint both admitted outer shadow layers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/box_shadow_wpt_spec.spl:255:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should paint a single inset shadow before the center fill' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
