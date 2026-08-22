# Revision-Driven Animation Advance

> Verifies the animation revision hot path behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Revision-Driven Animation Advance

Verifies the animation revision hot path behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/browser/feature/animation_revision_hot_path_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the animation revision hot path behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### REQ-WEB-BROWSER-004/006: revision-driven animation advance

#### keeps document-sized text out of the frame hot path

- Verify: keeps document-sized text out of the frame hot path
   - Artifact capture: after_step
- Open a CSS animation in the hosted BrowserSession
   - Artifact capture: after_step
- Render the exact initial Draw IR and Engine2D frame
   - Artifact capture: after_step
- Advance CSS and render the exact midpoint frame
   - Artifact capture: after_step
- Read the published frame through the production registry cache
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WEB-BROWSER-004/006
# @req: REQ-WEB-BROWSER-004 / REQ-006
# @req: REQ-WEB-BROWSER-004 REQ-WEB-BROWSER-006
step("Verify: keeps document-sized text out of the frame hot path")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("Open a CSS animation in the hosted BrowserSession")
var registry = HostedWebContentRegistry.create()
val html = (
    "<style>html,body{{margin:0}}@keyframes pulse{" +
    "from{{background-color:#dc2626}}" +
    "to{{background-color:#2563eb}}}" +
    "#stage{width:32px;height:24px;background-color:#dc2626;" +
    "animation:pulse 1000ms linear forwards}</style>" +
    "<div id='stage'></div>"
)
expect(registry.advance_window(
    901, html, WIDTH, HEIGHT, 1000, false
)).to_be(false)
expect(
    registry.sessions[0].browser.css_animation_instances.len()
).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

step("Render the exact initial Draw IR and Engine2D frame")
expect(_frame_receipt(
    registry.sessions[0], 0xFFDC2626u32
)).to_equal(
    "0|html_ast|1|1|rect:stage:0,0,32,24:4292617766|0|768"
)

step("Advance CSS and render the exact midpoint frame")
expect(registry.advance_window(
    901, html, WIDTH, HEIGHT, 1500, false
)).to_be(true)
expect(_frame_receipt(
    registry.sessions[0], 0xFF804488u32
)).to_equal(
    "500|html_ast|1|1|rect:stage:0,0,32,24:4286596232|0|768"
)

step("Read the published frame through the production registry cache")
expect(registry.body_html(901)).to_equal(
    registry.sessions[0].published_body_html
)
expect(_production_body_read_uses_published_cache()).to_be(true)
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

- Canonical SPipe generation for source `830f5195d56188a95adf54c639acea8255e6ce047ff802c2dc7ef75aea92a9fc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `830f5195d56188a95adf54c639acea8255e6ce047ff802c2dc7ef75aea92a9fc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `830f5195d56188a95adf54c639acea8255e6ce047ff802c2dc7ef75aea92a9fc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/browser/feature/animation_revision_hot_path_spec.spl
mirror: doc/06_spec/03_system/app/browser/feature/animation_revision_hot_path_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/browser/feature/animation_revision_hot_path_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/03_system/app/browser/feature/animation_revision_hot_path_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/browser/feature/animation_revision_hot_path_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
