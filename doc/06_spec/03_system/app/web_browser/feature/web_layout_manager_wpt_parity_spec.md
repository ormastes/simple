# WPT-derived web layout manager parity corpus

> Runs the existing bounded Web Platform Test witnesses through the browser CPU

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WPT-derived web layout manager parity corpus

Runs the existing bounded Web Platform Test witnesses through the browser CPU

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the existing bounded Web Platform Test witnesses through the browser CPU
oracle and retained layout manager.  Each case requires exact full/incremental
boxes, fragments, line boxes, overflow, and dependency-closed dirty-island
receipts.

Fixture provenance is retained beside each case.  This corpus does not claim
the complete upstream WPT suite.

## Scenarios

### REQ-WLM-003..REQ-WLM-005 WPT-derived parity corpus

#### should preserve exact block flex and grid layout artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WLM-003..REQ-WLM-005
```

</details>

#### should preserve exact positioned overflow and wrapped Latin artifacts

- should preserve exact positioned overflow and wrapped Latin artifacts
- Run the existing absolute-position witness
- Run the existing scrolling-overflow witness
- Run the existing wrapped Latin text witness


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve exact positioned overflow and wrapped Latin artifacts")
step("Run the existing absolute-position witness")
# Provenance: test/02_integration/rendering/simple_web_layout_child_index_spec.spl
_expect_wpt_layout_parity(
    "<style>html,body{{margin:0}}#host{position:relative;width:32px;" +
    "height:24px}#item{position:absolute;left:4px;top:3px;" +
    "width:12px;height:8px}</style><div id='host'>" +
    "<div id='item'></div></div>",
    104,
    "absolute-sticky"
)

step("Run the existing scrolling-overflow witness")
# Provenance: test/03_system/feature/web_platform/css/scrollbar_wpt_spec.spl
_expect_wpt_layout_parity(
    "<style>html,body{{margin:0}}#clip{width:32px;height:16px;" +
    "overflow:auto}#inner{width:64px;height:32px}</style>" +
    "<div id='clip'><div id='inner'></div></div>",
    105,
    "scroll"
)

step("Run the existing wrapped Latin text witness")
# Provenance: test/03_system/feature/web_platform/css/pseudo_text_wpt_spec.spl
_expect_wpt_layout_parity(
    "<style>html,body{{margin:0}}#line{display:block;width:40px;" +
    "font-size:8px;white-space:normal}</style>" +
    "<div id='line'>alpha beta gamma delta</div>",
    106,
    "inline"
)
```

</details>

#### should retain paint-only epochs and limit layout-change receipts

- should retain paint-only epochs and limit layout-change receipts
- Retain the initial production render and framework epoch
   - Expected: session.current_web_layout_run.unwrap().epoch equals `1`
- Apply a paint-only scroll without advancing layout epoch
   - Expected: painted.raw_boxes.bx.len() equals `initial.raw_boxes.bx.len()`
   - Expected: session.current_web_layout_run.unwrap().epoch equals `1`
- Change only the Flex geometry and inspect the exact receipt
   - Expected: changed.raw_boxes.bx.len() equals `initial.raw_boxes.bx.len()`
   - Expected: run.epoch equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain paint-only epochs and limit layout-change receipts")
val before_html = (
    "<style>html,body{{margin:0}}#flex{display:flex;width:24px}" +
    "#grid{display:grid;width:24px;grid-template-columns:12px 12px}" +
    ".item{width:8px;height:4px}</style>" +
    "<div id='flex'><div class='item'></div></div>" +
    "<div id='grid'><div class='item'></div></div>"
)
val after_html = before_html.replace(
    "#flex{display:flex;width:24px}",
    "#flex{display:flex;width:20px}"
)
val overlay = browser_text_input_overlay_empty()
val session = SimpleWebRenderSession.create()

step("Retain the initial production render and framework epoch")
val initial = session.render(
    _wpt_render_snapshot(201, 1, 1, 1, Some(before_html)),
    320, 240, 0, 0, overlay, [], []
)
expect(initial.raw_boxes.bx.len()).to_be_greater_than(0)
expect(session.current_web_layout_run.unwrap().epoch).to_equal(1)

step("Apply a paint-only scroll without advancing layout epoch")
val painted = session.render(
    _wpt_render_snapshot(201, 1, 1, 1, nil),
    320, 240, 0, 1, overlay, [], []
)
expect(painted.raw_boxes.bx.len()).to_equal(initial.raw_boxes.bx.len())
expect(session.current_web_layout_run.unwrap().epoch).to_equal(1)

step("Change only the Flex geometry and inspect the exact receipt")
val changed = session.render(
    _wpt_render_snapshot(201, 1, 2, 1, Some(after_html)),
    320, 240, 0, 1, overlay, [], []
)
expect(changed.raw_boxes.bx.len()).to_equal(initial.raw_boxes.bx.len())
val run = session.current_web_layout_run.unwrap()
val snapshot = session.current_web_layout_snapshot.unwrap()
val flex_id = _wpt_target_id(snapshot.nodes, "flex")
expect(run.epoch).to_equal(2)
expect(run.layout.receipt.visited_island_ids).to_equal(
    _wpt_expected_visited(snapshot.nodes, flex_id)
)
expect(run.layout.receipt.visited_island_ids.len()).to_be_less_than(
    run.layout.islands.len()
)
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
- `REQ-WLM-003..REQ-WLM-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `842cd8284d1e6f4fe7d497b05e74a03e2f8e36ba42d140ff7f52fb62f90772dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `842cd8284d1e6f4fe7d497b05e74a03e2f8e36ba42d140ff7f52fb62f90772dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `842cd8284d1e6f4fe7d497b05e74a03e2f8e36ba42d140ff7f52fb62f90772dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl
mirror: doc/06_spec/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=75 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl:158:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should preserve exact block flex and grid layout artifacts' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve exact block flex and grid layout artifacts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl:196:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve exact positioned overflow and wrapped Latin artifacts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl:196:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve exact positioned overflow and wrapped Latin artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl:231:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain paint-only epochs and limit layout-change receipts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl:231:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain paint-only epochs and limit layout-change receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
