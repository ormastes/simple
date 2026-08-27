# CSS `@supports` conditions

> Proves ASCII-insensitive admitted declaration and selector conditions through

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS `@supports` conditions

Proves ASCII-insensitive admitted declaration and selector conditions through

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves ASCII-insensitive admitted declaration and selector conditions through
the production Web semantic/layout owner, canonical Draw IR, Engine2D, and
the compatibility renderer. Conditions deeper than 32 fail closed.

## Scenarios

### Production CSS @supports conditions

#### should validate mixed-case properties values and selectors

- should validate mixed-case properties values and selectors
   - Artifact capture: after_step
- Resolve supported and rejected conditions in Web semantics
   - Artifact capture: after_step
   - Evidence: artifact verified by 2 expected checks
   - Expected: inspected.hit_index.boxes.bw[accepted_node] equals `12`
   - Expected: inspected.hit_index.boxes.by[unsupported_node] equals `24`
- Lower the exact condition winners through canonical Draw IR
   - Artifact capture: after_step
- Read identical exact pixels from Engine2D and compatibility
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: compatibility_pixels equals `engine_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 142 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should validate mixed-case properties values and selectors")
val html = (
    "<style>html,body{margin:0;background:#fff}" +
    "div{width:12px;height:8px}" +
    "#accepted{{background:#dc2626}}" +
    "#rejected{{background:#16a34a}}" +
    "#selector{{background:#ea580c}}" +
    "#unsupported{{background:#dc2626}}" +
    "@supports ((DISPLAY:FlEx) and (WIDTH:12PX)){" +
    "#accepted{{background:#2563eb}}}" +
    "@supports (display:definitely-not-css){\n" +
    "@layer guarded{\n#rejected{background:#9333ea}\n}\n}" +
    "@supports selector(div:has(.badge)){" +
    "#selector{{background:#0e7490}}}" +
    "@supports selector(div:popover-open){" +
    "#unsupported{{background:#9333ea}}}" +
    "@unknown guarded{\n#unsupported{background:#9333ea}\n}" +
    "</style>" +
    "<div id='accepted'></div><div id='rejected'></div>" +
    "<div id='selector'><span class='badge'></span></div>" +
    "<div id='unsupported'></div>"
)
val inspected = simple_web_layout_render_html_draw_ir_result(
    html, WIDTH, HEIGHT
)
val accepted_node = _supports_node_index(
    inspected.hit_index.nodes, "accepted"
)
val rejected_node = _supports_node_index(
    inspected.hit_index.nodes, "rejected"
)
val selector_node = _supports_node_index(
    inspected.hit_index.nodes, "selector"
)
val unsupported_node = _supports_node_index(
    inspected.hit_index.nodes, "unsupported"
)
if (
    accepted_node < 0 or rejected_node < 0 or selector_node < 0 or
    unsupported_node < 0
):
    fail("missing required semantic node")
for node_index in [
    accepted_node, rejected_node, selector_node, unsupported_node
]:
    if (
        node_index >= inspected.hit_index.styles.len() or
        node_index >= inspected.hit_index.boxes.by.len()
    ):
        fail("semantic node outside style/layout arrays")

step("Resolve supported and rejected conditions in Web semantics")
expect(inspected.hit_index.styles[accepted_node].bg).to_equal(
    0xFF2563EBu32
)
expect(inspected.hit_index.styles[rejected_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.styles[selector_node].bg).to_equal(
    0xFF0E7490u32
)
expect(inspected.hit_index.styles[unsupported_node].bg).to_equal(
    0xFFDC2626u32
)
expect(inspected.hit_index.boxes.bw[accepted_node]).to_equal(12)
expect(inspected.hit_index.boxes.by[unsupported_node]).to_equal(24)

step("Lower the exact condition winners through canonical Draw IR")
val composition = inspected.composition
if composition.batches.len() == 0:
    fail("missing Draw IR batch")
val commands = composition.batches[0].commands
val accepted_index = _supports_command_index(commands, "accepted")
val rejected_index = _supports_command_index(commands, "rejected")
val selector_index = _supports_command_index(commands, "selector")
val unsupported_index = _supports_command_index(
    commands, "unsupported"
)
if (
    accepted_index < 0 or rejected_index < 0 or
    selector_index < 0 or unsupported_index < 0
):
    fail("missing required Draw IR command")
val accepted = commands[accepted_index]
val rejected = commands[rejected_index]
val selector = commands[selector_index]
val unsupported = commands[unsupported_index]
expect([
    accepted.x, accepted.y, accepted.width, accepted.height
]).to_equal([0, 0, 12, 8])
expect([
    rejected.x, rejected.y, rejected.width, rejected.height
]).to_equal([0, 8, 12, 8])
expect([
    selector.x, selector.y, selector.width, selector.height
]).to_equal([0, 16, 12, 8])
expect([
    unsupported.x, unsupported.y,
    unsupported.width, unsupported.height
]).to_equal([0, 24, 12, 8])
expect(_supports_style(
    accepted, "background-color"
)).to_equal("4280640491")
expect(_supports_style(
    rejected, "background-color"
)).to_equal("4279673674")
expect(_supports_style(
    selector, "background-color"
)).to_equal("4279137424")
expect(_supports_style(
    unsupported, "background-color"
)).to_equal("4292617766")

step("Read identical exact pixels from Engine2D and compatibility")
val raster = Engine2dCompositorBackend.create_named(
    WIDTH, HEIGHT, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(WIDTH * HEIGHT)
val engine_pixels = rendered.pixels
val compatibility_pixels = BrowserRenderer.create(
    WIDTH, HEIGHT
).render_html_to_pixels(html).pixel_data
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 2
)).to_equal(0xFF2563EBu32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 10
)).to_equal(0xFF16A34Au32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 18
)).to_equal(0xFF0E7490u32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 26
)).to_equal(0xFFDC2626u32)
expect(_supports_count_color(
    engine_pixels, 0xFF9333EAu32
)).to_equal(0)
expect(compatibility_pixels).to_equal(engine_pixels)
```

</details>

#### should distinguish unsupported conditions from malformed grammar

- should distinguish unsupported conditions from malformed grammar
   - Artifact capture: after_step
- Reject malformed grammar while inverting valid unsupported forms
   - Artifact capture: after_step
- Apply only valid condition winners in Web semantics
   - Artifact capture: after_step
- Preserve validity-aware cascade results in canonical Draw IR
   - Artifact capture: after_step
- Read exact validity-aware pixels through both production paths
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `WIDTH * HEIGHT`
   - Expected: compatibility_pixels equals `engine_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 168 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should distinguish unsupported conditions from malformed grammar")
val html = (
    "<style>html,body{margin:0;background:#fff}" +
    "div{width:12px;height:8px}" +
    "#malformed{{background:#16a34a}}" +
    "#mixed{{background:#ea580c}}" +
    "#property{{background:#dc2626}}" +
    "#selector-valid{{background:#dc2626}}" +
    "#general{{background:#dc2626}}" +
    "@supports not garbage{#malformed{background:#9333ea}}" +
    "@supports (display:flex) or garbage{" +
    "#malformed{{background:#9333ea}}}" +
    "@supports garbage or (display:flex){" +
    "#malformed{{background:#9333ea}}}" +
    "@supports (display:flex) and (width:12px) or " +
    "(position:fixed){#mixed{background:#9333ea}}" +
    "@supports not (future-property:value){" +
    "#property{{background:#2563eb}}}" +
    "@supports not selector(div:popover-open){" +
    "#selector-valid{{background:#0e7490}}}" +
    "@supports not future(foo){#general{background:#7c3aed}}" +
    "</style><div id='malformed'></div><div id='mixed'></div>" +
    "<div id='property'></div><div id='selector-valid'></div>" +
    "<div id='general'></div>"
)
val inspected = simple_web_layout_render_html_draw_ir_result(
    html, WIDTH, HEIGHT
)
val malformed_node = _supports_node_index(
    inspected.hit_index.nodes, "malformed"
)
val mixed_node = _supports_node_index(
    inspected.hit_index.nodes, "mixed"
)
val property_node = _supports_node_index(
    inspected.hit_index.nodes, "property"
)
val selector_valid_node = _supports_node_index(
    inspected.hit_index.nodes, "selector-valid"
)
val general_node = _supports_node_index(
    inspected.hit_index.nodes, "general"
)
for node_index in [
    malformed_node, mixed_node, property_node,
    selector_valid_node, general_node
]:
    if (
        node_index < 0 or
        node_index >= inspected.hit_index.styles.len()
    ):
        fail("missing supports-validity semantic node")

step("Reject malformed grammar while inverting valid unsupported forms")
expect(eval_supports_query("not garbage")).to_be(false)
expect(eval_supports_query(
    "(display:flex) or garbage"
)).to_be(false)
expect(eval_supports_query(
    "garbage or (display:flex)"
)).to_be(false)
expect(eval_supports_query(
    "(display:flex) and garbage"
)).to_be(false)
expect(eval_supports_query(
    "garbage and (display:flex)"
)).to_be(false)
expect(eval_supports_query(
    "(display:flex) and (width:12px) or (position:fixed)"
)).to_be(false)
expect(eval_supports_query(
    "not selector(div >)"
)).to_be(false)
expect(eval_supports_query(
    "not (future-property:value)"
)).to_be(true)
expect(eval_supports_query(
    "not selector(div:popover-open)"
)).to_be(true)
expect(eval_supports_query("not future(foo)")).to_be(true)
expect(eval_supports_query(
    "(display:flex) and (width:12px)"
)).to_be(true)
expect(eval_supports_query(
    "(display:invalid) or (position:fixed)"
)).to_be(true)

step("Apply only valid condition winners in Web semantics")
expect(inspected.hit_index.styles[malformed_node].bg).to_equal(
    0xFF16A34Au32
)
expect(inspected.hit_index.styles[mixed_node].bg).to_equal(
    0xFFEA580Cu32
)
expect(inspected.hit_index.styles[property_node].bg).to_equal(
    0xFF2563EBu32
)
expect(inspected.hit_index.styles[selector_valid_node].bg).to_equal(
    0xFF0E7490u32
)
expect(inspected.hit_index.styles[general_node].bg).to_equal(
    0xFF7C3AEDu32
)

step("Preserve validity-aware cascade results in canonical Draw IR")
val composition = inspected.composition
if composition.batches.len() == 0:
    fail("missing supports-validity Draw IR batch")
val commands = composition.batches[0].commands
val malformed = commands[_supports_command_index(
    commands, "malformed"
)]
val mixed = commands[_supports_command_index(commands, "mixed")]
val property = commands[_supports_command_index(
    commands, "property"
)]
val selector_valid = commands[_supports_command_index(
    commands, "selector-valid"
)]
val general = commands[_supports_command_index(commands, "general")]
expect(_supports_style(
    malformed, "background-color"
)).to_equal("4279673674")
expect(_supports_style(
    mixed, "background-color"
)).to_equal("4293548044")
expect(_supports_style(
    property, "background-color"
)).to_equal("4280640491")
expect(_supports_style(
    selector_valid, "background-color"
)).to_equal("4279137424")
expect(_supports_style(
    general, "background-color"
)).to_equal("4286331629")

step("Read exact validity-aware pixels through both production paths")
val raster = Engine2dCompositorBackend.create_named(
    WIDTH, HEIGHT, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(WIDTH * HEIGHT)
val engine_pixels = rendered.pixels
val compatibility_pixels = BrowserRenderer.create(
    WIDTH, HEIGHT
).render_html_to_pixels(html).pixel_data
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 2
)).to_equal(0xFF16A34Au32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 10
)).to_equal(0xFFEA580Cu32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 18
)).to_equal(0xFF2563EBu32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 26
)).to_equal(0xFF0E7490u32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 34
)).to_equal(0xFF7C3AEDu32)
expect(_supports_count_color(
    engine_pixels, 0xFF9333EAu32
)).to_equal(0)
expect(compatibility_pixels).to_equal(engine_pixels)
```

</details>

#### should admit depth thirty-two and reject deeper malformed chains

- should admit depth thirty-two and reject deeper malformed chains
   - Artifact capture: after_step
- Apply the boundary condition and reject every over-budget form
   - Artifact capture: after_step
- Preserve boundary decisions in layout and canonical Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 1 expected check
   - Expected: inspected.hit_index.boxes.bw[limit_node] equals `12`
- Read exact boundary pixels through both production paths
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: rendered.pixels.len() equals `WIDTH * 24`
   - Expected: compatibility_pixels equals `engine_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 120 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should admit depth thirty-two and reject deeper malformed chains")
val admitted = _nested_supports_condition(31)
val rejected = _nested_supports_condition(32)
val html = (
    "<style>html,body{margin:0;background:#fff}" +
    "div{width:12px;height:8px}" +
    "#limit{{background:#16a34a}}#over{{background:#ea580c}}" +
    "@supports " + admitted + "{#limit{background:#2563eb}}" +
    "@supports " + rejected + "{#over{background:#9333ea}}" +
    "</style><div id='limit'></div><div id='over'></div>"
)
val inspected = simple_web_layout_render_html_draw_ir_result(
    html, WIDTH, 24
)
val limit_node = _supports_node_index(
    inspected.hit_index.nodes, "limit"
)
val over_node = _supports_node_index(
    inspected.hit_index.nodes, "over"
)
if limit_node < 0 or over_node < 0:
    fail("missing required semantic node")
for node_index in [limit_node, over_node]:
    if (
        node_index >= inspected.hit_index.styles.len() or
        node_index >= inspected.hit_index.boxes.bw.len()
    ):
        fail("semantic node outside style/layout arrays")

step("Apply the boundary condition and reject every over-budget form")
expect(eval_supports_query(admitted)).to_be(true)
expect(eval_supports_query(rejected)).to_be(false)
expect(eval_supports_query(_supports_and_chain(32))).to_be(true)
expect(eval_supports_query(_supports_and_chain(33))).to_be(false)
expect(eval_supports_query(
    "(display:definitely-not-css) or (display:flex)"
)).to_be(true)
expect(eval_supports_query(
    "not (display:definitely-not-css)"
)).to_be(true)
expect(eval_supports_query("not (display:flex)")).to_be(false)
# RED: cycle2 admitted invalid functional/generic values.
expect(eval_supports_query("(width:12potato)")).to_be(false)
expect(eval_supports_query("(color:#ggg)")).to_be(false)
expect(eval_supports_query("(color:rgb(potato))")).to_be(false)
expect(eval_supports_query("(opacity:banana)")).to_be(false)
expect(eval_supports_query("(position:sideways)")).to_be(false)
expect(eval_supports_query(
    "(transform:rotate(potato))"
)).to_be(false)
expect(eval_supports_query(
    "selector(div:hovered)"
)).to_be(false)
expect(eval_supports_query(
    "selector(div:island(.card))"
)).to_be(false)
expect(eval_supports_query(
    "selector(div:is(.card)"
)).to_be(false)
expect(eval_supports_query("selector(div >)")).to_be(false)
expect(eval_supports_query("selector(div[)")).to_be(false)
expect(eval_supports_query("selector(div,,span)")).to_be(false)
expect(eval_supports_query("selector(div(foo))")).to_be(false)
expect(eval_supports_query("selector(:root[)")).to_be(false)
expect(eval_supports_query("selector(@@@)")).to_be(false)
expect(eval_supports_query("selector(div!)")).to_be(false)
expect(eval_supports_query("selector(:is(a,,b))")).to_be(false)
expect(eval_supports_query("selector(:root[])")).to_be(false)
expect(eval_supports_query(
    "not not not not not not not not not not not not not not " +
    "not not not not not not not not not not not not not not " +
    "not not not not not (display:flex)"
)).to_be(false)
expect(eval_supports_query("((display:flex)")).to_be(false)
expect(inspected.hit_index.styles[limit_node].bg).to_equal(
    0xFF2563EBu32
)
expect(inspected.hit_index.styles[over_node].bg).to_equal(
    0xFFEA580Cu32
)

step("Preserve boundary decisions in layout and canonical Draw IR")
expect(inspected.hit_index.boxes.bw[limit_node]).to_equal(12)
val composition = inspected.composition
if composition.batches.len() == 0:
    fail("missing Draw IR batch")
val commands = composition.batches[0].commands
val limit_index = _supports_command_index(commands, "limit")
val over_index = _supports_command_index(commands, "over")
if limit_index < 0 or over_index < 0:
    fail("missing required Draw IR command")
val limit = commands[limit_index]
val over = commands[over_index]
expect(_supports_style(
    limit, "background-color"
)).to_equal("4280640491")
expect(_supports_style(
    over, "background-color"
)).to_equal("4293548044")

step("Read exact boundary pixels through both production paths")
val raster = Engine2dCompositorBackend.create_named(
    WIDTH, 24, "software"
)
val rendered = raster.render_draw_ir_composition(composition, [])
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(rendered.pixels.len()).to_equal(WIDTH * 24)
val engine_pixels = rendered.pixels
val compatibility_pixels = BrowserRenderer.create(
    WIDTH, 24
).render_html_to_pixels(html).pixel_data
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 2
)).to_equal(0xFF2563EBu32)
expect(_supports_pixel_at(
    engine_pixels, WIDTH, 2, 10
)).to_equal(0xFFEA580Cu32)
expect(compatibility_pixels).to_equal(engine_pixels)
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

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-002`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb26d76cdc5ae785207c8a3c13efb45916c2a32e4e3e484acffa9741f425b9cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb26d76cdc5ae785207c8a3c13efb45916c2a32e4e3e484acffa9741f425b9cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb26d76cdc5ae785207c8a3c13efb45916c2a32e4e3e484acffa9741f425b9cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/at_supports_wpt_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=85 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/css/at_supports_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/at_supports_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:94:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should validate mixed-case properties values and selectors' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should validate mixed-case properties values and selectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:241:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should distinguish unsupported conditions from malformed grammar' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:241:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should distinguish unsupported conditions from malformed grammar' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:414:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should admit depth thirty-two and reject deeper malformed chains' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/at_supports_wpt_spec.spl:414:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should admit depth thirty-two and reject deeper malformed chains' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
