# menu_element_rendering_spec

> Selected `<menu>` UA list spacing through Web semantics, Draw IR, and Engine2D.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# menu_element_rendering_spec

Selected `<menu>` UA list spacing through Web semantics, Draw IR, and Engine2D.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/html/menu_element_rendering_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Selected `<menu>` UA list spacing through Web semantics, Draw IR, and Engine2D.

Plan: `doc/03_plan/sys_test/html_css_spec_traceability.md`

use std.spec.*
use common.ui.draw_ir.{DrawIrCommand, DrawIrComposition}
use os.compositor.compositor_engine2d.{Engine2dCompositorBackend}
use std.gc_async_mut.gpu.browser_engine.dom_accessors.{
    be_dom_get_tag, be_dom_path_for_route
}
use std.gc_async_mut.gpu.browser_engine.html_tree_builder.{
    html_tree_builder_build
}
use std.gc_async_mut.gpu.browser_engine.simple_web_html_layout_renderer.{
    HNode, SimpleWebLayoutDrawIrResult,
    simple_web_layout_render_html_draw_ir_result
}
use test.system.browser_dom_identity_helpers.{system_dom_identity_index, system_dom_route}

### Production menu element rendering

#### should lower menu UA list spacing through Draw IR to pixels

- should lower menu UA list spacing through Draw IR to pixels
   - GUI capture: after_step (HTML preferred when available)
- Parse menu as a body child
   - GUI capture: after_step (HTML preferred when available)
- Apply selected menu user-agent list spacing
   - GUI capture: after_step (HTML preferred when available)
- Lower the menu box to exact Draw IR geometry
   - GUI capture: after_step (HTML preferred when available)
- Rasterize the Draw IR menu box
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should lower menu UA list spacing through Draw IR to pixels")
val html = _menu_html()

fn _check_menu_semantics(html: text):
    val root = html_tree_builder_build(html)
    val identity_index = system_dom_identity_index(root)
    val menu_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "menu"))
    val body_path = be_dom_path_for_route(root, identity_index, system_dom_route(identity_index, "body"))
    expect(menu_path.len()).to_be_greater_than(1)
    expect(be_dom_get_tag(menu_path[menu_path.len() - 1])).to_equal("menu")
    expect(menu_path[menu_path.len() - 2].node_id).to_equal(
        body_path[body_path.len() - 1].node_id
    )

step("Apply selected menu user-agent list spacing")
val result = simple_web_layout_render_html_draw_ir_result(
    html, WIDTH, HEIGHT
)
_check_menu_ua_style(result)

step("Lower the menu box to exact Draw IR geometry")
_check_menu_draw_ir(result)

step("Rasterize the Draw IR menu box")
_check_menu_pixels(result)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b9c4bb8746e52558e30d80e0c0bf6d939fffbaedadced8df0a8cf0b0b1ff5156`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b9c4bb8746e52558e30d80e0c0bf6d939fffbaedadced8df0a8cf0b0b1ff5156`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b9c4bb8746e52558e30d80e0c0bf6d939fffbaedadced8df0a8cf0b0b1ff5156`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/feature/web_platform/html/menu_element_rendering_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/html/menu_element_rendering_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/html/menu_element_rendering_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/html/menu_element_rendering_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/html/menu_element_rendering_spec.spl:131:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should lower menu UA list spacing through Draw IR to pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/html/menu_element_rendering_spec.spl:131:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should lower menu UA list spacing through Draw IR to pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
