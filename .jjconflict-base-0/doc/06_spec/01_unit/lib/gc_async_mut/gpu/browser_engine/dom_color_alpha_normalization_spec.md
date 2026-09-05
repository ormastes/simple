# dom_color_alpha_normalization_spec

> CSS alpha grammar, validity, animation, Draw IR, and pixel propagation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dom_color_alpha_normalization_spec

CSS alpha grammar, validity, animation, Draw IR, and pixel propagation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

CSS alpha grammar, validity, animation, Draw IR, and pixel propagation.

## Scenarios

### CSS alpha number and percentage normalization

#### should parse complete bounded CSS numbers without integer overflow

- should parse complete bounded CSS numbers without integer overflow
- Accept signed fractions, percentages, and exponent forms
   - Expected: parse_color_value("rgba(1,2,3,+.5e0)") equals `0x01020380u32`
   - Expected: parse_color_value("rgb(1 2 3 / 5e-1)") equals `0x01020380u32`
   - Expected: parse_color_value("hsla(120,100%,50%,5E-1)") equals `0x00FF0080u32`
   - Expected: parse_color_value("hsl(120 100% 50% / 5E+1%)") equals `0x00FF0080u32`
- Clamp extreme exponents before byte conversion
   - Expected: parse_alpha_component_checked("1e999999") ?? 0u32 equals `255u32`
   - Expected: parse_alpha_component_checked("1e-999999") ?? 255u32 equals `0u32`
   - Expected: parse_alpha_component_checked("-1e999999") ?? 255u32 equals `0u32`
   - Expected: parse_alpha_component_checked("100.0001%") ?? 0u32 equals `255u32`
   - Expected: parse_alpha_component_checked("-0.1%") ?? 255u32 equals `0u32`
- Round beyond the former nine-digit truncation boundary
   - Expected: parse_alpha_component_checked("0.0019607844") ?? 0u32 equals `1u32`
   - Expected: parse_alpha_component_checked("0.0019607843") ?? 1u32 equals `0u32`
   - Expected: parse_alpha_component_checked("50.0%") ?? 0u32 equals `128u32`
- Leave the independent RGB channel parser unchanged
   - Expected: parse_color_component("50%") equals `127u32`
   - Expected: parse_color_value("rgba(1e2,2,3,.5)") equals `0x01020380u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should parse complete bounded CSS numbers without integer overflow")
step("Accept signed fractions, percentages, and exponent forms")
expect(parse_color_value("rgba(1,2,3,+.5e0)")).to_equal(0x01020380u32)
expect(parse_color_value("rgb(1 2 3 / 5e-1)")).to_equal(0x01020380u32)
expect(parse_color_value("hsla(120,100%,50%,5E-1)")).to_equal(0x00FF0080u32)
expect(parse_color_value("hsl(120 100% 50% / 5E+1%)")).to_equal(0x00FF0080u32)

step("Clamp extreme exponents before byte conversion")
expect(parse_alpha_component_checked("1e999999") ?? 0u32).to_equal(255u32)
expect(parse_alpha_component_checked("1e-999999") ?? 255u32).to_equal(0u32)
expect(parse_alpha_component_checked("-1e999999") ?? 255u32).to_equal(0u32)
expect(parse_alpha_component_checked("100.0001%") ?? 0u32).to_equal(255u32)
expect(parse_alpha_component_checked("-0.1%") ?? 255u32).to_equal(0u32)

step("Round beyond the former nine-digit truncation boundary")
expect(parse_alpha_component_checked("0.0019607844") ?? 0u32).to_equal(1u32)
expect(parse_alpha_component_checked("0.0019607843") ?? 1u32).to_equal(0u32)
expect(parse_alpha_component_checked("50.0%") ?? 0u32).to_equal(128u32)

step("Leave the independent RGB channel parser unchanged")
expect(parse_color_component("50%")).to_equal(127u32)
expect(parse_color_value("rgba(1e2,2,3,.5)")).to_equal(0x01020380u32)
```

</details>

#### should reject malformed alpha without replacing a valid keyframe winner

- should reject malformed alpha without replacing a valid keyframe winner
- Distinguish transparent alpha from malformed alpha
   - Expected: parse_color_value_checked("rgba(1,2,3,0)") ?? 0u32 equals `0x01020300u32`
   - Expected: parse_color_value("var(--theme-color)") equals `0x00000000u32`
- Cascade a later malformed duplicate behind the valid declaration
   - Expected: registry.entries.len() equals `1`
   - Expected: registry.entries[0].frames.len() equals `1`
   - Expected: registry.entries[0].frames[0].properties.len() equals `1`
   - Expected: color.r equals `34`
   - Expected: color.g equals `197`
   - Expected: color.b equals `94`
   - Expected: color.a equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject malformed alpha without replacing a valid keyframe winner")
step("Distinguish transparent alpha from malformed alpha")
expect(parse_color_value_checked("rgba(1,2,3,0)") ?? 0u32).to_equal(0x01020300u32)
expect(parse_color_value_checked("rgba(1,2,3,1.)")).to_be_nil()
expect(parse_color_value_checked("rgb(1 2 3 / 1e)")).to_be_nil()
expect(parse_color_value_checked("hsla(120,100%,50%,50 %)")).to_be_nil()
expect(parse_color_value_checked("hsl(120 100% 50% / --.5)")).to_be_nil()
expect(parse_color_value("var(--theme-color)")).to_equal(0x00000000u32)
expect(parse_color_value_checked("var(--theme-color)")).to_be_nil()

step("Cascade a later malformed duplicate behind the valid declaration")
val registry = extract_keyframes("""
    @keyframes retained {
        50% { background-color: rgba(34,197,94,5e-1); }
        50% { background-color: rgba(255,0,0,1e); }
    }
""")
expect(registry.entries.len()).to_equal(1)
expect(registry.entries[0].frames.len()).to_equal(1)
expect(registry.entries[0].frames[0].properties.len()).to_equal(1)
match registry.entries[0].frames[0].properties[0].value:
    CSSValue.Color(color):
        expect(color.r).to_equal(34)
        expect(color.g).to_equal(197)
        expect(color.b).to_equal(94)
        expect(color.a).to_equal(128)
    _:
        fail("expected the earlier valid color declaration")
```

</details>

#### should preserve exponent alpha through keyframes, Draw IR, and pixels

- should preserve exponent alpha through keyframes, Draw IR, and pixels
   - GUI capture: after_step (HTML preferred when available)
- Create one animation instance from exponent-alpha keyframes
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: instances.len() equals `1`
- Lower the animated opaque color to canonical Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: command.color equals `0xFF22C55Eu32`
- Rasterize identically to an opaque literal control
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: animated_pixels.len() equals `WIDTH * HEIGHT`
   - Expected: literal_pixels.len() equals `WIDTH * HEIGHT`
   - Expected: animated_pixels[6 * WIDTH + 8] equals `0xFF22C55Eu32`
   - Expected: animated_pixels equals `literal_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve exponent alpha through keyframes, Draw IR, and pixels")
step("Create one animation instance from exponent-alpha keyframes")
val html = _alpha_html(true)
val instances = simple_web_layout_reconcile_animation_instances(
    html, WIDTH, 0, 0, false, []
)
expect(instances.len()).to_equal(1)

step("Lower the animated opaque color to canonical Draw IR")
val result = (
    simple_web_layout_render_html_draw_ir_result_at_time_with_animations(
        html, WIDTH, HEIGHT, 0, instances
    )
)
val command = _command(result.composition, "box")
expect(command.color).to_equal(0xFF22C55Eu32)
expect([
    command.x, command.y, command.width, command.height
]).to_equal([0, 0, 16, 12])

step("Rasterize identically to an opaque literal control")
val animated_pixels = BrowserRenderer.create(
    WIDTH, HEIGHT
).render_html_to_pixels_at_time_with_animations(
    html, 0, instances
).pixel_data
val literal_pixels = BrowserRenderer.create(
    WIDTH, HEIGHT
).render_html_to_pixels(_alpha_html(false)).pixel_data
expect(animated_pixels.len()).to_equal(WIDTH * HEIGHT)
expect(literal_pixels.len()).to_equal(WIDTH * HEIGHT)
expect(animated_pixels[6 * WIDTH + 8]).to_equal(0xFF22C55Eu32)
expect(animated_pixels).to_equal(literal_pixels)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9621849f94114491d0358c46648ee7101c2153e9b7e84e0875d4befe527025bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9621849f94114491d0358c46648ee7101c2153e9b7e84e0875d4befe527025bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9621849f94114491d0358c46648ee7101c2153e9b7e84e0875d4befe527025bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse complete bounded CSS numbers without integer overflow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse complete bounded CSS numbers without integer overflow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl:88:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject malformed alpha without replacing a valid keyframe winner' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject malformed alpha without replacing a valid keyframe winner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl:122:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve exponent alpha through keyframes, Draw IR, and pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/dom_color_alpha_normalization_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve exponent alpha through keyframes, Draw IR, and pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
