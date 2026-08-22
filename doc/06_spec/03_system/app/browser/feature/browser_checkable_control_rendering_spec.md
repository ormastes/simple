# Browser checkbox and radio rendering

> Verifies the browser checkable control rendering behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser checkbox and radio rendering

Verifies the browser checkable control rendering behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/browser_checkable_control_rendering_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the browser checkable control rendering behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Production checkbox and radio rendering

#### should render live checked state through canonical Draw IR

- Verify: should render live checked state through canonical Draw IR
   - GUI capture: after_step (HTML preferred when available)
- Parse the interactive HTML document
   - GUI capture: after_step (HTML preferred when available)
- Resolve control semantics and layout
   - GUI capture: after_step (HTML preferred when available)
- Emit canonical Draw IR and event metadata
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: toggle_frame.color equals `CHECKABLE_SURFACE`
   - Expected: radio_indicator.parent_id equals `radio-a`
   - Expected: radio_indicator.color equals `CHECKABLE_ACCENT`
- Render and interact through the production browser
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 2 expected checks
   - Expected: checked_dispatch.event.target_tag equals `input`
   - Expected: disabled_dispatch.default_action equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 299 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-003 REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-007 REQ-WEB-BROWSER-008 REQ-WEB-BROWSER-021
step("Verify: should render live checked state through canonical Draw IR")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val html = checkable_fixture_html()

step("Parse the interactive HTML document")
val root = html_tree_builder_build(html)
val identity_index = system_dom_identity_index(root)
val toggle_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "toggle"))
val radio_a_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "radio-a"))
val radio_b_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "radio-b"))
val disabled_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "disabled"))
expect(be_dom_get_tag(
    toggle_path[toggle_path.len() - 1]
)).to_equal("input")
expect(be_dom_get_attr(
    toggle_path[toggle_path.len() - 1], "type"
)).to_equal("checkbox")
expect(be_dom_get_attr(
    radio_a_path[radio_a_path.len() - 1], "type"
)).to_equal("radio")
expect(be_dom_get_attr(
    radio_a_path[radio_a_path.len() - 1], "name"
)).to_equal("choice")
expect(be_dom_get_attr(
    radio_b_path[radio_b_path.len() - 1], "name"
)).to_equal("choice")
expect(be_dom_has_attr(
    toggle_path[toggle_path.len() - 1], "checked"
)).to_be(false)
expect(be_dom_has_attr(
    radio_a_path[radio_a_path.len() - 1], "checked"
)).to_be(true)
expect(be_dom_has_attr(
    radio_b_path[radio_b_path.len() - 1], "checked"
)).to_be(false)
expect(be_dom_has_attr(
    disabled_path[disabled_path.len() - 1], "disabled"
)).to_be(true)
expect(be_dom_has_attr(
    disabled_path[disabled_path.len() - 1], "checked"
)).to_be(false)
var session = BrowserSession.new()
expect(session.open_html(
    "https://example.test/checkable-controls", html
).is_ok()).to_be(true)
val session_identity_index = system_browser_dom_identity_index(session)

step("Resolve control semantics and layout")
val initial = checkable_render(session)
val toggle_index = checkable_node_index(
    initial.hit_index.nodes, "toggle"
)
val radio_a_index = checkable_node_index(
    initial.hit_index.nodes, "radio-a"
)
val radio_b_index = checkable_node_index(
    initial.hit_index.nodes, "radio-b"
)
val disabled_index = checkable_node_index(
    initial.hit_index.nodes, "disabled"
)
expect([
    initial.hit_index.boxes.bx[toggle_index],
    initial.hit_index.boxes.by[toggle_index],
    initial.hit_index.boxes.bw[toggle_index],
    initial.hit_index.boxes.bh[toggle_index]
]).to_equal([2, 2, 14, 14])
expect([
    initial.hit_index.boxes.bx[radio_a_index],
    initial.hit_index.boxes.by[radio_a_index],
    initial.hit_index.boxes.bw[radio_a_index],
    initial.hit_index.boxes.bh[radio_a_index]
]).to_equal([22, 2, 14, 14])
expect([
    initial.hit_index.boxes.bx[radio_b_index],
    initial.hit_index.boxes.by[radio_b_index],
    initial.hit_index.boxes.bw[radio_b_index],
    initial.hit_index.boxes.bh[radio_b_index]
]).to_equal([42, 2, 14, 14])
expect([
    initial.hit_index.boxes.bx[disabled_index],
    initial.hit_index.boxes.by[disabled_index],
    initial.hit_index.boxes.bw[disabled_index],
    initial.hit_index.boxes.bh[disabled_index]
]).to_equal([62, 2, 14, 14])
expect(initial.hit_index.styles[toggle_index].accent_color).to_equal(
    CHECKABLE_ACCENT
)
expect(initial.hit_index.styles[toggle_index].caret_color).to_equal(
    CHECKABLE_CARET
)
expect(
    initial.hit_index.styles[toggle_index].accent_color ==
    initial.hit_index.styles[toggle_index].caret_color
).to_be(false)
expect(simple_web_layout_hit_test_index(
    initial.hit_index, 9, 9
)).to_equal("id:toggle")
expect(simple_web_layout_hit_test_index(
    initial.hit_index, 29, 9
)).to_equal("id:radio-a")
expect(simple_web_layout_hit_test_index(
    initial.hit_index, 49, 9
)).to_equal("id:radio-b")

step("Emit canonical Draw IR and event metadata")
val toggle_frame = checkable_frame(
    initial.composition, "toggle_checkable_frame", "toggle"
)
expect([
    toggle_frame.x, toggle_frame.y,
    toggle_frame.width, toggle_frame.height
]).to_equal([2, 2, 14, 14])
expect(toggle_frame.color).to_equal(CHECKABLE_SURFACE)
expect(checkable_style(
    toggle_frame, "input-type"
)).to_equal("checkbox")
expect(checkable_style(
    toggle_frame, "checked"
)).to_equal("false")
expect(checkable_style(
    toggle_frame, "accent-color"
)).to_equal("{CHECKABLE_ACCENT}")
expect(checkable_has_style(
    toggle_frame, "border-radius"
)).to_be(false)
expect(checkable_has_command(
    initial.composition, "toggle_checked_indicator"
)).to_be(false)
expect(checkable_has_command(
    initial.composition, "radio-a_checked_indicator"
)).to_be(true)
expect(checkable_has_command(
    initial.composition, "radio-b_checked_indicator"
)).to_be(false)
expect(checkable_has_command(
    initial.composition, "disabled_checked_indicator"
)).to_be(false)
val radio_a_frame = checkable_frame(
    initial.composition, "radio-a_checkable_frame", "radio-a"
)
val radio_b_frame = checkable_frame(
    initial.composition, "radio-b_checkable_frame", "radio-b"
)
val disabled_frame = checkable_frame(
    initial.composition, "disabled_checkable_frame", "disabled"
)
expect(checkable_style(
    disabled_frame, "checked"
)).to_equal("false")
val radio_indicator = checkable_command(
    initial.composition, "radio-a_checked_indicator"
)
expect(radio_indicator.component_id).to_equal(
    "radio-a_checked_indicator"
)
expect(radio_indicator.parent_id).to_equal("radio-a")
expect(checkable_style(
    radio_a_frame, "border-radius"
)).to_equal("7")
expect(checkable_style(
    radio_b_frame, "border-radius"
)).to_equal("7")
expect(checkable_style(
    radio_indicator, "border-radius"
)).to_equal("4")
expect(radio_indicator.color).to_equal(CHECKABLE_ACCENT)
expect([
    radio_indicator.clip_rect.x, radio_indicator.clip_rect.y,
    radio_indicator.clip_rect.width,
    radio_indicator.clip_rect.height
]).to_equal([0, 0, CHECKABLE_WIDTH, CHECKABLE_HEIGHT])
expect(checkable_has_style(
    disabled_frame, "border-radius"
)).to_be(false)

step("Render and interact through the production browser")
val initial_pixels = session.render_to_pixels(
    CHECKABLE_WIDTH, CHECKABLE_HEIGHT
).pixel_data
expect(initial_pixels.len()).to_equal(
    CHECKABLE_WIDTH * CHECKABLE_HEIGHT
)
expect(checkable_pixel(initial_pixels, 2, 2)).to_equal(
    CHECKABLE_ACCENT
)
expect(checkable_pixel(initial_pixels, 22, 2)).to_equal(
    CHECKABLE_PAGE
)
expect(checkable_pixel(initial_pixels, 29, 2)).to_equal(
    CHECKABLE_ACCENT
)
expect(checkable_center_pixel(initial_pixels, 9)).to_equal(
    CHECKABLE_SURFACE
)
expect(checkable_center_pixel(initial_pixels, 29)).to_equal(
    CHECKABLE_ACCENT
)
expect(checkable_center_pixel(initial_pixels, 49)).to_equal(
    CHECKABLE_SURFACE
)

val checked_dispatch = session.dispatch_dom_event(
    "toggle", "click", true, true
)
expect(session_identity_index.author_id_for_route(
    checked_dispatch.target_route
) ?? "").to_equal("toggle")
expect(checked_dispatch.event.target_tag).to_equal("input")
expect(checked_dispatch.default_action).to_equal(
    "input-checkbox-toggle"
)
expect(checkable_checked(session, "toggle")).to_be(true)
val checked_result = checkable_render(session)
expect(checkable_has_command(
    checked_result.composition, "toggle_checked_indicator"
)).to_be(true)
val checked_pixels = session.render_to_pixels(
    CHECKABLE_WIDTH, CHECKABLE_HEIGHT
).pixel_data
expect(checkable_center_pixel(checked_pixels, 9)).to_equal(
    CHECKABLE_ACCENT
)

val unchecked_dispatch = session.dispatch_dom_event(
    "toggle", "click", true, true
)
expect(session_identity_index.author_id_for_route(
    unchecked_dispatch.target_route
) ?? "").to_equal("toggle")
expect(checkable_checked(session, "toggle")).to_be(false)
val unchecked_result = checkable_render(session)
expect(checkable_has_command(
    unchecked_result.composition, "toggle_checked_indicator"
)).to_be(false)
val unchecked_pixels = session.render_to_pixels(
    CHECKABLE_WIDTH, CHECKABLE_HEIGHT
).pixel_data
expect(checkable_center_pixel(unchecked_pixels, 9)).to_equal(
    CHECKABLE_SURFACE
)
expect(checkable_pixels_equal(
    unchecked_pixels, initial_pixels
)).to_be(true)

val radio_dispatch = session.dispatch_dom_event(
    "radio-b", "click", true, true
)
expect(session_identity_index.author_id_for_route(
    radio_dispatch.target_route
) ?? "").to_equal("radio-b")
expect(radio_dispatch.default_action).to_equal(
    "input-radio-select"
)
expect(checkable_checked(session, "radio-a")).to_be(false)
expect(checkable_checked(session, "radio-b")).to_be(true)
val selected = checkable_render(session)
expect(checkable_has_command(
    selected.composition, "radio-a_checked_indicator"
)).to_be(false)
expect(checkable_has_command(
    selected.composition, "radio-b_checked_indicator"
)).to_be(true)
val selected_pixels = session.render_to_pixels(
    CHECKABLE_WIDTH, CHECKABLE_HEIGHT
).pixel_data
expect(checkable_center_pixel(selected_pixels, 29)).to_equal(
    CHECKABLE_SURFACE
)
expect(checkable_center_pixel(selected_pixels, 49)).to_equal(
    CHECKABLE_ACCENT
)
expect(checkable_pixels_equal(
    selected_pixels, initial_pixels
)).to_be(false)

val disabled_dispatch = session.dispatch_dom_event(
    "disabled", "click", true, true
)
expect(session_identity_index.author_id_for_route(
    disabled_dispatch.target_route
) ?? "").to_equal("disabled")
expect(disabled_dispatch.default_action).to_equal("")
expect(disabled_dispatch.default_action_allowed).to_be(false)
expect(checkable_checked(session, "disabled")).to_be(false)
val disabled_result = checkable_render(session)
expect(checkable_has_command(
    disabled_result.composition, "disabled_checked_indicator"
)).to_be(false)
val disabled_pixels = session.render_to_pixels(
    CHECKABLE_WIDTH, CHECKABLE_HEIGHT
).pixel_data
expect(checkable_center_pixel(disabled_pixels, 69)).to_equal(
    CHECKABLE_SURFACE
)
expect(checkable_pixels_equal(
    disabled_pixels, selected_pixels
)).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cdac483ac341f14d39793f444ef7d5467a2f317eee00279624bbf4b248b4d5c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cdac483ac341f14d39793f444ef7d5467a2f317eee00279624bbf4b248b4d5c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cdac483ac341f14d39793f444ef7d5467a2f317eee00279624bbf4b248b4d5c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/browser_checkable_control_rendering_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/browser_checkable_control_rendering_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/browser_checkable_control_rendering_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/browser_checkable_control_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/browser_checkable_control_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/browser/feature/browser_checkable_control_rendering_spec.spl:161:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render live checked state through canonical Draw IR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
