# CSS Inline-Block Formatting

> Proves the production HTML/CSS layout owner preserves `display:inline-block`,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Inline-Block Formatting

Proves the production HTML/CSS layout owner preserves `display:inline-block`,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the production HTML/CSS layout owner preserves `display:inline-block`,
places atomic boxes beside each other in one inline formatting run, and emits
their exact border boxes through canonical Draw IR before pixel execution.

## Scenarios

### Production Simple Web inline-block formatting

#### should keep inline-block border boxes in one atomic inline run

- should keep inline-block border boxes in one atomic inline run
   - Protocol capture: after_step
- Resolve inline-block as the computed display value
   - Protocol capture: after_step
- Lay out exact atomic border boxes on one line
   - Protocol capture: after_step
- Lower the same absolute boxes through canonical Draw IR
   - Protocol capture: after_step
   - Evidence: protocol response verified by 9 expected checks
   - Expected: _style_value(first, "display") equals `inline-block`
   - Expected: first.x equals `0`
   - Expected: first.y equals `0`
   - Expected: first.width equals `26`
   - Expected: first.height equals `18`
   - Expected: second.x equals `26`
   - Expected: second.y equals `0`
   - Expected: second.width equals `26`
   - Expected: second.height equals `18`
- Read exact interior and control pixels through Engine2D
   - Protocol capture: after_step
   - Evidence: protocol response verified by 4 expected checks
   - Expected: pixels[20 + 12 * 80] equals `0xFFDC2626u32`
   - Expected: pixels[46 + 12 * 80] equals `0xFF2563EBu32`
   - Expected: pixels[60 + 3 * 80] equals `0xFFFFFFFFu32`
   - Expected: pixels[10 + 21 * 80] equals `0xFFFFFFFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep inline-block border boxes in one atomic inline run")
step("Resolve inline-block as the computed display value")
expect(simple_web_layout_debug_style_by_id(
    INLINE_BLOCK_HTML, "first", "display"
)).to_equal("inline-block")
expect(simple_web_layout_debug_style_by_id(
    INLINE_BLOCK_HTML, "second", "display"
)).to_equal("inline-block")

step("Lay out exact atomic border boxes on one line")
expect(simple_web_layout_debug_layout_by_id(
    INLINE_BLOCK_HTML, 80, 48, "first", "x"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    INLINE_BLOCK_HTML, 80, 48, "first", "y"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    INLINE_BLOCK_HTML, 80, 48, "first", "w"
)).to_equal("26")
expect(simple_web_layout_debug_layout_by_id(
    INLINE_BLOCK_HTML, 80, 48, "first", "h"
)).to_equal("18")
expect(simple_web_layout_debug_layout_by_id(
    INLINE_BLOCK_HTML, 80, 48, "second", "x"
)).to_equal("26")
expect(simple_web_layout_debug_layout_by_id(
    INLINE_BLOCK_HTML, 80, 48, "second", "y"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    INLINE_BLOCK_HTML, 80, 48, "after", "y"
)).to_equal("18")

step("Lower the same absolute boxes through canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir(
    INLINE_BLOCK_HTML, 80, 48
)
val first = _command_by_id(
    composition.batches[0].commands, "first"
)
val second = _command_by_id(
    composition.batches[0].commands, "second"
)
expect(_style_value(first, "display")).to_equal("inline-block")
expect(first.x).to_equal(0)
expect(first.y).to_equal(0)
expect(first.width).to_equal(26)
expect(first.height).to_equal(18)
expect(second.x).to_equal(26)
expect(second.y).to_equal(0)
expect(second.width).to_equal(26)
expect(second.height).to_equal(18)

step("Read exact interior and control pixels through Engine2D")
val pixels = BrowserRenderer.create(80, 48).render_html_to_pixels(
    INLINE_BLOCK_HTML
).pixel_data
expect(pixels[20 + 12 * 80]).to_equal(0xFFDC2626u32)
expect(pixels[46 + 12 * 80]).to_equal(0xFF2563EBu32)
expect(pixels[60 + 3 * 80]).to_equal(0xFFFFFFFFu32)
expect(pixels[10 + 21 * 80]).to_equal(0xFFFFFFFFu32)
```

</details>

#### should align empty baseline inline-block bottom edges through canonical Draw IR

- should align empty baseline inline-block bottom edges through canonical Draw IR
   - Protocol capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Protocol capture: after_step
- Resolve baseline alignment in computed Style
   - Protocol capture: after_step
- Lay out empty atomic inline-blocks on their shared baseline
   - Protocol capture: after_step
- Preserve baseline geometry in canonical Draw IR before pixels
   - Protocol capture: after_step
   - Evidence: protocol response verified by 8 expected checks
   - Expected: _style_value(short, "vertical-align") equals `baseline`
   - Expected: _style_value(tall, "vertical-align") equals `baseline`
   - Expected: _style_value(short, "line-height") equals `18`
   - Expected: short.y equals `12`
   - Expected: tall.y equals `0`
   - Expected: short.y + short.height equals `20`
   - Expected: tall.y + tall.height equals `20`
   - Expected: after.y equals `23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should align empty baseline inline-block bottom edges through canonical Draw IR")
step("Render HTML and CSS through canonical Draw IR")
val html = (
    "<style>html,body{margin:0;padding:0;width:64px}" +
    ".item{display:inline-block;width:8px;margin:0;padding:0;" +
    "border:0;vertical-align:baseline}" +
    "#short{height:8px;background:#dc2626}" +
    "#tall{height:20px;background:#2563eb}" +
    "#after{display:block;width:8px;height:4px;background:#16a34a}" +
    "</style><span id='short' class='item'></span>" +
    "<span id='tall' class='item'></span><div id='after'></div>"
)

step("Resolve baseline alignment in computed Style")
expect(simple_web_layout_debug_style_by_id(
    html, "short", "vertical-align"
)).to_equal("baseline")
expect(simple_web_layout_debug_style_by_id(
    html, "tall", "vertical-align"
)).to_equal("baseline")

step("Lay out empty atomic inline-blocks on their shared baseline")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "short", "h"
)).to_equal("8")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "tall", "h"
)).to_equal("20")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "tall", "y"
)).to_equal("0")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "short", "y"
)).to_equal("12")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "after", "y"
)).to_equal("23")

step("Preserve baseline geometry in canonical Draw IR before pixels")
val composition = simple_web_layout_render_html_draw_ir(html, 64, 48)
val short = _command_by_id(composition.batches[0].commands, "short")
val tall = _command_by_id(composition.batches[0].commands, "tall")
val after = _command_by_id(composition.batches[0].commands, "after")
expect(_style_value(short, "vertical-align")).to_equal("baseline")
expect(_style_value(tall, "vertical-align")).to_equal("baseline")
expect(_style_value(short, "line-height")).to_equal("18")
expect(short.y).to_equal(12)
expect(tall.y).to_equal(0)
expect(short.y + short.height).to_equal(20)
expect(tall.y + tall.height).to_equal(20)
expect(after.y).to_equal(23)
```

</details>

#### should include the parent strut text and vertical margins in an empty inline-block baseline line

- should include the parent strut text and vertical margins in an empty inline-block baseline line
   - Protocol capture: after_step
- Render HTML and CSS through canonical Draw IR
   - Protocol capture: after_step
- Resolve parent and atomic baseline semantics in computed Style
   - Protocol capture: after_step
- Lay out the shared strut baseline and bottom margin edges
   - Protocol capture: after_step
- Preserve the shared baseline geometry in canonical Draw IR
   - Protocol capture: after_step
   - Evidence: protocol response verified by 6 expected checks
   - Expected: _style_value(label, "line-height") equals `12`
   - Expected: short.y equals `14`
   - Expected: tall.y equals `1`
   - Expected: label.y equals `13`
   - Expected: short.y + short.height + 3 equals `25`
   - Expected: tall.y + tall.height + 4 equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should include the parent strut text and vertical margins in an empty inline-block baseline line")
step("Render HTML and CSS through canonical Draw IR")
val html = (
    "<style>html,body{margin:0;padding:0;width:64px;font-size:16px;" +
    "line-height:12px}.item{display:inline-block;width:8px;padding:0;" +
    "border:0;vertical-align:baseline}#short{height:8px;margin:2px 0 3px;" +
    "background:#dc2626}#tall{height:20px;margin:1px 0 4px;" +
    "background:#2563eb}#label{{background:#facc15}}#after{display:block;" +
    "width:8px;height:4px;background:#16a34a}</style>" +
    "<span id='short' class='item'></span><span id='tall' class='item'></span>" +
    "<span id='label'>X</span><div id='after'></div>"
)

step("Resolve parent and atomic baseline semantics in computed Style")
expect(simple_web_layout_debug_style_by_id(
    html, "short", "vertical-align"
)).to_equal("baseline")
expect(simple_web_layout_debug_style_by_id(
    html, "tall", "vertical-align"
)).to_equal("baseline")
expect(simple_web_layout_debug_style_by_id(
    html, "label", "vertical-align"
)).to_equal("baseline")

step("Lay out the shared strut baseline and bottom margin edges")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "short", "y"
)).to_equal("14")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "tall", "y"
)).to_equal("1")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "label", "y"
)).to_equal("13")
expect(simple_web_layout_debug_layout_by_id(
    html, 64, 48, "after", "y"
)).to_equal("25")

step("Preserve the shared baseline geometry in canonical Draw IR")
val composition = simple_web_layout_render_html_draw_ir(html, 64, 48)
val short = _command_by_id(composition.batches[0].commands, "short")
val tall = _command_by_id(composition.batches[0].commands, "tall")
val label = _command_by_id(composition.batches[0].commands, "label")
expect(_style_value(label, "line-height")).to_equal("12")
expect(short.y).to_equal(14)
expect(tall.y).to_equal(1)
expect(label.y).to_equal(13)
expect(short.y + short.height + 3).to_equal(25)
expect(tall.y + tall.height + 4).to_equal(25)
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `18f5efcb169f140f358a6758f5d783380f6a21bc457c1c3b47f0be12e796c3ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18f5efcb169f140f358a6758f5d783380f6a21bc457c1c3b47f0be12e796c3ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18f5efcb169f140f358a6758f5d783380f6a21bc457c1c3b47f0be12e796c3ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/inline_block_wpt_spec.md (current)
findings: 10 blockers: 1
  narrative=100 structure=85 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/css/inline_block_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/inline_block_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:57:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep inline-block border boxes in one atomic inline run' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep inline-block border boxes in one atomic inline run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should align empty baseline inline-block bottom edges through canonical Draw IR' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should align empty baseline inline-block bottom edges through canonical Draw IR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:180:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include the parent strut text and vertical margins in an empty inline-block baseline line' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/web_platform/css/inline_block_wpt_spec.spl:180:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include the parent strut text and vertical margins in an empty inline-block baseline line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
