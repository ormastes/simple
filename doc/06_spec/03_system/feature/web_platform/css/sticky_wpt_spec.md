# CSS Sticky Positioning

> Proves bounded root-scroll `position: sticky; top:<px>` through Web layout,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Sticky Positioning

Proves bounded root-scroll `position: sticky; top:<px>` through Web layout,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/sticky_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves bounded root-scroll `position: sticky; top:<px>` through Web layout,
canonical Draw IR, and exact expected-color Engine2D coverage/count. Nested
scrollports, finite wrappers, other inset axes, nested sticky roots, and
containing-block bottom constraints remain RED.

## Scenarios

### REQ-WEB-BROWSER-003/004: CSS sticky positioning

#### should pin one top-inset sticky subtree during root scrolling

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WEB-BROWSER-003/004
```

</details>

#### should leave unsupported sticky declarations in normal scrolled flow

- should leave unsupported sticky declarations in normal scrolled flow
   - Expected: _sticky_style(command, "top") equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should leave unsupported sticky declarations in normal scrolled flow")
for inset in [
    "", "top:auto;", "inset:auto;", "inset-block:auto;",
    "inset-block-start:auto;",
    "top:0;transform:translateY(2px);",
    "top:0;transform:skewX(10deg);",
    "top:0;translate:0 2px;"
]:
    val html = (
        "<style>html,body{{margin:0}}#spacer{height:4px}" +
        "#probe{position:sticky;" + inset +
        "width:4px;height:4px;background:#2563eb}" +
        "#tail{height:20px}</style><div id='spacer'></div>" +
        "<div id='probe'></div><div id='tail'></div>"
    )
    expect(simple_web_layout_debug_style_by_id(
        html, "probe", "position"
    )).to_equal("sticky")
    val result =
        simple_web_layout_render_html_draw_ir_result_with_overlay_at_scroll_time(
            html, 16, 12, 0, 6,
            browser_text_input_overlay_empty()
        )
    val index = _sticky_command_index(
        result.composition.batches[0].commands, "probe"
    )
    expect(index).to_be_greater_than(-1)
    if index >= 0:
        val command = result.composition.batches[0].commands[index]
        expect([command.x, command.y, command.width, command.height]).to_equal(
            [0, -2, 4, 4]
        )
        expect(_sticky_style(command, "top")).to_equal("auto")
    val raster = Engine2dCompositorBackend.create_named(
        16, 12, "software"
    )
    val frame = raster.render_draw_ir_composition(
        result.composition, []
    )
    raster.shutdown()
    expect(_sticky_color_count(
        frame.pixels, 0xFF2563EBu32
    )).to_equal(8)
```

</details>

#### should not root-pin sticky nodes inside finite or scrolling wrappers

- should not root-pin sticky nodes inside finite or scrolling wrappers
   - Expected: command.parent_id equals `wrapper`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should not root-pin sticky nodes inside finite or scrolling wrappers")
for wrapper_style in [
    "height:8px;", "height:8px;overflow-y:scroll;"
]:
    val html = (
        "<style>html,body{{margin:0}}#wrapper{" + wrapper_style +
        "}#spacer{height:4px}#probe{position:sticky;top:0;" +
        "width:4px;height:4px;background:#2563eb}" +
        "#inner-tail{height:20px}#outer-tail{height:20px}</style>" +
        "<div id='wrapper'><div id='spacer'></div>" +
        "<div id='probe'></div><div id='inner-tail'></div></div>" +
        "<div id='outer-tail'></div>"
    )
    val result =
        simple_web_layout_render_html_draw_ir_result_with_overlay_at_scroll_time(
            html, 16, 12, 0, 6,
            browser_text_input_overlay_empty()
        )
    val index = _sticky_command_index(
        result.composition.batches[0].commands, "probe"
    )
    expect(index).to_be_greater_than(-1)
    if index >= 0:
        val command = result.composition.batches[0].commands[index]
        expect([command.x, command.y, command.width, command.height]).to_equal(
            [0, -2, 4, 4]
        )
        expect(command.parent_id).to_equal("wrapper")
    val raster = Engine2dCompositorBackend.create_named(
        16, 12, "software"
    )
    val frame = raster.render_draw_ir_composition(
        result.composition, []
    )
    raster.shutdown()
    expect(_sticky_color_count(
        frame.pixels, 0xFF2563EBu32
    )).to_equal(8)
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
- `REQ-WEB-BROWSER-003/004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ab6fc5a45c60c85aed0107e04b9406b8fe237cbfb03b879eded644c336fad3cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ab6fc5a45c60c85aed0107e04b9406b8fe237cbfb03b879eded644c336fad3cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ab6fc5a45c60c85aed0107e04b9406b8fe237cbfb03b879eded644c336fad3cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/web_platform/css/sticky_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/sticky_wpt_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/sticky_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/sticky_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/sticky_wpt_spec.spl:67:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should pin one top-inset sticky subtree during root scrolling' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/sticky_wpt_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should pin one top-inset sticky subtree during root scrolling' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/sticky_wpt_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should leave unsupported sticky declarations in normal scrolled flow' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/sticky_wpt_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should leave unsupported sticky declarations in normal scrolled flow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/sticky_wpt_spec.spl:210:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should not root-pin sticky nodes inside finite or scrolling wrappers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/sticky_wpt_spec.spl:210:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should not root-pin sticky nodes inside finite or scrolling wrappers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
