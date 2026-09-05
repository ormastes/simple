# CSS `aspect-ratio` Canonical Rendering

> This bounded scenario exercises the production HTML/CSS path for both width-led

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS `aspect-ratio` Canonical Rendering

This bounded scenario exercises the production HTML/CSS path for both width-led

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

This bounded scenario exercises the production HTML/CSS path for both width-led
and height-led aspect ratios: HTML semantics, resolved layout, Draw IR, and
Engine2D pixels. It is source/spec/manual evidence only until an admitted
pure-Simple runner executes it.

## Scenarios

### REQ-WEB-BROWSER-003/004/021: CSS aspect-ratio

#### resolves width-led and height-led ratios through Engine2D

- resolve width-led and height-led ratios through Engine2D
   - Artifact capture: after_step
- Resolve width-led and height-led ratios in canonical web layout
   - Artifact capture: after_step
- Retain both ratio boxes in canonical HTML semantics and Draw IR
   - Artifact capture: after_step
   - Evidence: artifact verified by 5 expected checks
   - Expected: result.composition.batches[0].source.source_kind equals `html_ast`
   - Expected: [wide.x, wide.y, wide.width, wide.height] equals `[0, 0, 32, 16]`
   - Expected: [tall.x, tall.y, tall.width, tall.height] equals `[0, 16, 12, 24]`
   - Expected: _aspect_style(wide, "aspect-ratio") equals `2 / 1`
   - Expected: _aspect_style(tall, "aspect-ratio") equals `1 / 2`
- Render ratio-resolved Draw IR through the canonical Engine2D backend
   - Artifact capture: after_step
   - Evidence: artifact verified by 3 expected checks
   - Expected: rendered.skipped_command_count equals `0`
   - Expected: _aspect_color_count(rendered.pixels, 0xFF2563EBu32) equals `512`
   - Expected: _aspect_color_count(rendered.pixels, 0xFFDC2626u32) equals `288`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-003/004/021
step("resolve width-led and height-led ratios through Engine2D")
step("Resolve width-led and height-led ratios in canonical web layout")
expect(simple_web_layout_debug_layout_by_id(
    ASPECT_RATIO_HTML, 64, 64, "wide", "w"
)).to_equal("32")
expect(simple_web_layout_debug_layout_by_id(
    ASPECT_RATIO_HTML, 64, 64, "wide", "h"
)).to_equal("16")
expect(simple_web_layout_debug_layout_by_id(
    ASPECT_RATIO_HTML, 64, 64, "tall", "w"
)).to_equal("12")
expect(simple_web_layout_debug_layout_by_id(
    ASPECT_RATIO_HTML, 64, 64, "tall", "h"
)).to_equal("24")

step("Retain both ratio boxes in canonical HTML semantics and Draw IR")
val result = simple_web_layout_render_html_draw_ir_result(
    ASPECT_RATIO_HTML, 64, 64
)
val wide = _aspect_command(result, "wide")
val tall = _aspect_command(result, "tall")
expect(result.composition.batches[0].source.source_kind).to_equal("html_ast")
expect([wide.x, wide.y, wide.width, wide.height]).to_equal([0, 0, 32, 16])
expect([tall.x, tall.y, tall.width, tall.height]).to_equal([0, 16, 12, 24])
expect(_aspect_style(wide, "aspect-ratio")).to_equal("2 / 1")
expect(_aspect_style(tall, "aspect-ratio")).to_equal("1 / 2")

step("Render ratio-resolved Draw IR through the canonical Engine2D backend")
val raster = Engine2dCompositorBackend.create_named(64, 64, "software")
val rendered = raster.render_draw_ir_composition(
    result.composition, []
)
raster.shutdown()
expect(rendered.skipped_command_count).to_equal(0)
expect(_aspect_color_count(rendered.pixels, 0xFF2563EBu32)).to_equal(512)
expect(_aspect_color_count(rendered.pixels, 0xFFDC2626u32)).to_equal(288)
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
- `REQ-WEB-BROWSER-003/004/021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `821f0b44357254a7c2176565fef5d688a29909ff0cc3439b0e9699a96a87b4f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `821f0b44357254a7c2176565fef5d688a29909ff0cc3439b0e9699a96a87b4f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `821f0b44357254a7c2176565fef5d688a29909ff0cc3439b0e9699a96a87b4f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/css/aspect_ratio_wpt_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves width-led and height-led ratios through Engine2D' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
