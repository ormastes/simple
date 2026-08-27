# details_summary_rendering_spec

> `details`/`summary` disclosure rendering through Web semantics and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# details_summary_rendering_spec

`details`/`summary` disclosure rendering through Web semantics and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

`details`/`summary` disclosure rendering through Web semantics and Engine2D.

The bounded selected profile does not synthesize the user-agent shadow
`summary` for a closed `details` that omits one; it hides that element's
children. The first authored direct `summary`, click toggle, open state, and
nested independent state are implemented.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

## Scenarios

### Production details and summary rendering

#### should render the default disclosure marker through canonical Draw IR

- should render the default disclosure marker through canonical Draw IR
   - GUI capture: after_step (HTML preferred when available)
- Parse the authored disclosure summary
   - GUI capture: after_step (HTML preferred when available)
- Resolve the default disclosure marker state
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: _geometry(closed, "label")[0] equals `16`
   - Expected: _geometry(opened, "label")[0] equals `16`
   - Expected: _geometry(authored, "label")[0] equals `16`
   - Expected: _geometry(blocked, "label")[0] equals `0`
- Emit canonical disclosure marker Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 10 expected checks
   - Expected: closed_marker.kind equals `text`
   - Expected: closed_marker.text_value equals `▶`
   - Expected: [closed_marker.x, closed_marker.y] equals `[0, 0]`
   - Expected: closed_marker.parent_id equals `summary`
   - Expected: open_marker.kind equals `text`
   - Expected: open_marker.text_value equals `▼`
   - Expected: [open_marker.x, open_marker.y] equals `[0, 0]`
   - Expected: open_marker.parent_id equals `summary`
   - Expected: authored_marker.text_value equals `▶`
   - Expected: [authored_marker.x, authored_marker.y] equals `[0, 0]`
- Render exact closed and open Engine2D pixels
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 1 expected check
   - Expected: _non_white_pixel_count(blocked_pixels) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 124 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render the default disclosure marker through canonical Draw IR")
val closed_html = setup_summary_marker_fixture(false, "", "More")
val open_html = setup_summary_marker_fixture(true, "", "More")
val authored_html = setup_summary_marker_fixture(
    false, "list-item", "More"
)
val block_html = setup_summary_marker_fixture(
    false, "block", "More"
)

step("Parse the authored disclosure summary")
val root = html_tree_builder_build(closed_html)
val identity_index = system_dom_identity_index(root)
val details_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "disclosure")
)
val summary_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "summary")
)
expect(be_dom_get_tag(
    summary_path[summary_path.len() - 1]
)).to_equal("summary")
expect(summary_path[
    summary_path.len() - 1
].parent_id).to_equal(details_path[details_path.len() - 1].node_id)

step("Resolve the default disclosure marker state")
val closed = simple_web_layout_render_html_draw_ir_result(
    closed_html, WIDTH, HEIGHT
)
val opened = simple_web_layout_render_html_draw_ir_result(
    open_html, WIDTH, HEIGHT
)
val blocked = simple_web_layout_render_html_draw_ir_result(
    block_html, WIDTH, HEIGHT
)
val authored = simple_web_layout_render_html_draw_ir_result(
    authored_html, WIDTH, HEIGHT
)
expect(closed.hit_index.styles[
    _node_index(closed.hit_index.nodes, "summary")
].display).to_equal("list-item")
expect(opened.hit_index.styles[
    _node_index(opened.hit_index.nodes, "summary")
].display).to_equal("list-item")
expect(blocked.hit_index.styles[
    _node_index(blocked.hit_index.nodes, "summary")
].display).to_equal("block")
expect(authored.hit_index.styles[
    _node_index(authored.hit_index.nodes, "summary")
].display).to_equal("list-item")
expect(_geometry(closed, "label")[0]).to_equal(16)
expect(_geometry(opened, "label")[0]).to_equal(16)
expect(_geometry(authored, "label")[0]).to_equal(16)
expect(_geometry(blocked, "label")[0]).to_equal(0)

step("Emit canonical disclosure marker Draw IR")
val closed_marker = _command(
    closed.composition, "summary::marker"
)
val open_marker = _command(
    opened.composition, "summary::marker"
)
val authored_marker = _command(
    authored.composition, "summary::marker"
)
expect(closed_marker.kind).to_equal("text")
expect(closed_marker.text_value).to_equal("▶")
expect([closed_marker.x, closed_marker.y]).to_equal([0, 0])
expect(closed_marker.parent_id).to_equal("summary")
expect(_style(
    closed_marker, "summary-marker-state"
)).to_equal("closed")
expect(open_marker.kind).to_equal("text")
expect(open_marker.text_value).to_equal("▼")
expect([open_marker.x, open_marker.y]).to_equal([0, 0])
expect(open_marker.parent_id).to_equal("summary")
expect(_style(
    open_marker, "summary-marker-state"
)).to_equal("open")
expect(authored_marker.text_value).to_equal("▶")
expect([authored_marker.x, authored_marker.y]).to_equal([0, 0])
expect(_style(
    authored_marker, "summary-marker-state"
)).to_equal("closed")
expect(_has_command(
    blocked.composition, "summary::marker"
)).to_be(false)

step("Render exact closed and open Engine2D pixels")
val closed_pixels = _pixels(
    simple_web_layout_render_html_draw_ir_result(
        setup_summary_marker_fixture(false, "", ""),
        WIDTH, HEIGHT
    )
)
val open_pixels = _pixels(
    simple_web_layout_render_html_draw_ir_result(
        setup_summary_marker_fixture(true, "", ""),
        WIDTH, HEIGHT
    )
)
val authored_pixels = _pixels(
    simple_web_layout_render_html_draw_ir_result(
        setup_summary_marker_fixture(false, "list-item", ""),
        WIDTH, HEIGHT
    )
)
val blocked_pixels = _pixels(
    simple_web_layout_render_html_draw_ir_result(
        setup_summary_marker_fixture(false, "block", ""),
        WIDTH, HEIGHT
    )
)
expect(_non_white_pixel_count(closed_pixels)).to_be_greater_than(0)
expect(_non_white_pixel_count(open_pixels)).to_be_greater_than(0)
expect(_pixel_difference_count(
    closed_pixels, open_pixels
)).to_be_greater_than(0)
expect(_pixel_difference_count(
    closed_pixels, authored_pixels
)).to_equal(0)
expect(_non_white_pixel_count(blocked_pixels)).to_equal(0)
```

</details>

#### should preserve disclosure semantics through events and exact pixels

- should preserve disclosure semantics through events and exact pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse details and summary semantics
   - GUI capture: after_step (HTML preferred when available)
- Render a closed disclosure
   - GUI capture: after_step (HTML preferred when available)
- Open the disclosure through the canonical event path
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 8 expected checks
   - Expected: dispatch.default_action equals `details-toggle`
   - Expected: dispatch.default_action_allowed is true
   - Expected: dispatch.actions.len() equals `0`
   - Expected: canceled.default_action equals `details-toggle`
   - Expected: canceled.event.default_prevented is true
   - Expected: canceled.default_action_allowed is false
   - Expected: link_dispatch.default_action equals `navigate:/safe`
   - Expected: button_dispatch.default_action equals `button-activate`
- Render nested disclosure pixels
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 166 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve disclosure semantics through events and exact pixels")
val html = setup_details_summary_fixture()

step("Parse details and summary semantics")
val root = html_tree_builder_build(html)
val identity_index = system_dom_identity_index(root)
val details_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "disclosure")
)
val summary_path = be_dom_path_for_route(
    root, identity_index, system_dom_route(identity_index, "summary")
)
expect(be_dom_get_tag(
    details_path[details_path.len() - 1]
)).to_equal("details")
expect(be_dom_get_tag(
    summary_path[summary_path.len() - 1]
)).to_equal("summary")
expect(summary_path[
    summary_path.len() - 1
].parent_id).to_equal(details_path[details_path.len() - 1].node_id)
val malformed = html_tree_builder_build(
    "<body id='malformed-body'><p id='before-details'>before" +
    "<details id='malformed-details'><summary></summary></details>" +
    "<p id='before-summary'>before" +
    "<summary id='loose-summary'></summary></body>"
)
val malformed_index = system_dom_identity_index(malformed)
val malformed_body = be_dom_path_for_route(
    malformed, malformed_index,
    system_dom_route(malformed_index, "malformed-body")
)
val malformed_details = be_dom_path_for_route(
    malformed, malformed_index,
    system_dom_route(malformed_index, "malformed-details")
)
val loose_summary = be_dom_path_for_route(
    malformed, malformed_index,
    system_dom_route(malformed_index, "loose-summary")
)
expect(malformed_details[
    malformed_details.len() - 1
].parent_id).to_equal(
    malformed_body[malformed_body.len() - 1].node_id
)
expect(loose_summary[
    loose_summary.len() - 1
].parent_id).to_equal(
    malformed_body[malformed_body.len() - 1].node_id
)

step("Render a closed disclosure")
check_closed_summary_only(html)

step("Open the disclosure through the canonical event path")
val dispatch = be_dom_dispatch_event_to_route(
    root, identity_index,
    system_dom_route(identity_index, "summary-label"),
    "click", true, true, true
)
expect(dispatch.default_action).to_equal("details-toggle")
expect(dispatch.default_action_allowed).to_equal(true)
expect(dispatch.actions.len()).to_equal(0)
val opened = be_dom_apply_default_action_to_route(
    root, identity_index, dispatch.target_route, dispatch.default_action
)
val opened_path = be_dom_path_for_route(
    opened, identity_index,
    system_dom_route(identity_index, "disclosure")
)
expect(be_dom_has_attr(
    opened_path[opened_path.len() - 1], "open"
)).to_equal(true)
check_open_content_visible(
    be_dom_serialize_html_for_render(opened)
)
val canceled_root = html_tree_builder_build(
    "<details id='canceled-details'><summary>" +
    "<span id='cancel-target' onclick='prevent-default'></span>" +
    "</summary><div></div></details>"
)
val canceled_index = system_dom_identity_index(canceled_root)
val canceled = be_dom_dispatch_event_to_route(
    canceled_root, canceled_index,
    system_dom_route(canceled_index, "cancel-target"),
    "click", true, true, true
)
expect(canceled.default_action).to_equal("details-toggle")
expect(canceled.event.default_prevented).to_equal(true)
expect(canceled.default_action_allowed).to_equal(false)
val canceled_after = if canceled.default_action_allowed:
    be_dom_apply_default_action_to_route(
        canceled_root, canceled_index, canceled.target_route,
        canceled.default_action
    )
else:
    canceled_root
val canceled_details = be_dom_path_for_route(
    canceled_after, canceled_index,
    system_dom_route(canceled_index, "canceled-details")
)
expect(be_dom_has_attr(
    canceled_details[canceled_details.len() - 1], "open"
)).to_equal(false)
val interactive_root = html_tree_builder_build(
    "<details id='interactive-details'><summary>" +
    "<a id='summary-link' href='/safe'>" +
    "<span id='link-target'></span></a>" +
    "<button id='summary-button' type='button'>" +
    "<span id='button-target'></span></button>" +
    "</summary><div></div></details>"
)
val interactive_index = system_dom_identity_index(interactive_root)
val link_dispatch = be_dom_dispatch_event_to_route(
    interactive_root, interactive_index,
    system_dom_route(interactive_index, "link-target"),
    "click", true, true, true
)
expect(link_dispatch.default_action).to_equal("navigate:/safe")
val linked = be_dom_apply_default_action_to_route(
    interactive_root, interactive_index, link_dispatch.target_route,
    link_dispatch.default_action
)
val link_path = be_dom_path_for_route(
    linked, interactive_index,
    system_dom_route(interactive_index, "summary-link")
)
val linked_details = be_dom_path_for_route(
    linked, interactive_index,
    system_dom_route(interactive_index, "interactive-details")
)
expect(be_dom_get_attr(
    link_path[link_path.len() - 1], "data-navigation"
)).to_equal("/safe")
expect(be_dom_has_attr(
    linked_details[linked_details.len() - 1], "open"
)).to_equal(false)

val button_dispatch = be_dom_dispatch_event_to_route(
    interactive_root, interactive_index,
    system_dom_route(interactive_index, "button-target"),
    "click", true, true, true
)
expect(button_dispatch.default_action).to_equal("button-activate")
val activated = be_dom_apply_default_action_to_route(
    interactive_root, interactive_index, button_dispatch.target_route,
    button_dispatch.default_action
)
val button_path = be_dom_path_for_route(
    activated, interactive_index,
    system_dom_route(interactive_index, "summary-button")
)
val activated_details = be_dom_path_for_route(
    activated, interactive_index,
    system_dom_route(interactive_index, "interactive-details")
)
expect(be_dom_get_attr(
    button_path[button_path.len() - 1], "data-activated"
)).to_equal("true")
expect(be_dom_has_attr(
    activated_details[activated_details.len() - 1], "open"
)).to_equal(false)

step("Render nested disclosure pixels")
check_nested_disclosure_independent()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bde534af056f794bc00f4afefa45f474f1a41c1abd0b186ebfae02dc4f6177f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bde534af056f794bc00f4afefa45f474f1a41c1abd0b186ebfae02dc4f6177f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bde534af056f794bc00f4afefa45f474f1a41c1abd0b186ebfae02dc4f6177f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/details_summary_rendering_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/details_summary_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/details_summary_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl:291:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render the default disclosure marker through canonical Draw IR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl:291:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render the default disclosure marker through canonical Draw IR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl:423:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve disclosure semantics through events and exact pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl:423:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve disclosure semantics through events and exact pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
