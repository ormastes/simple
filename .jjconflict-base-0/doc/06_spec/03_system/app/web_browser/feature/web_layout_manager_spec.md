# Web layout manager

> Adapts the real browser CPU oracle, classifies invalidation, delegates full

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web layout manager

Adapts the real browser CPU oracle, classifies invalidation, delegates full

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/web_browser/feature/web_layout_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Adapts the real browser CPU oracle, classifies invalidation, delegates full
and incremental work to the structural framework, and qualifies hit regions
by DOM generation and layout epoch.

## Scenarios

### REQ-WLM-001..REQ-WLM-007 web layout manager

#### pre-rejects complex-script GPU line breaking before submission

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-WLM-001..REQ-WLM-007
```

</details>

#### preserves the browser oracle through incremental framework execution

- preserves the browser oracle through incremental framework execution
- Capture the CPU layout oracle
   - Expected: adapted.fault equals ``
   - Expected: adapted.snapshot.nodes.len() equals `browser.raw_boxes.bx.len()`
   - Expected: adapted.snapshot.text_results.len() equals `adapted.snapshot.text_requests.len()`
   - Expected: node.id equals `index + 1`
   - Expected: node.arena_index equals `index`
   - Expected: node.dom_route_id equals `index`
   - Expected: adapted.snapshot.oracle_boxes[index].x equals `browser.raw_boxes.bx[index] as i64`
   - Expected: adapted.snapshot.oracle_boxes[index].y equals `browser.raw_boxes.by[index] as i64`
   - Expected: adapted.snapshot.oracle_boxes[index].width equals `browser.raw_boxes.bw[index] as i64`
   - Expected: adapted.snapshot.oracle_boxes[index].height equals `browser.raw_boxes.bh[index] as i64`
- Classify browser layout islands
   - Expected: frontier.invalidated_ids equals `[flex_id]`
- Apply the invalidated frontier
   - Expected: full.result.fault equals ``
   - Expected: incremental.result.fault equals ``
   - Expected: full.result.layout.fragments equals `adapted.snapshot.oracle_fragments`
   - Expected: full.result.layout.line_boxes equals `adapted.snapshot.oracle_line_boxes`
   - Expected: full.result.layout.overflows equals `adapted.snapshot.oracle_overflows`
   - Expected: incremental.result.layout.boxes equals `full.result.layout.boxes`
   - Expected: incremental.result.layout.fragments equals `full.result.layout.fragments`
   - Expected: incremental.result.layout.line_boxes equals `full.result.layout.line_boxes`
   - Expected: incremental.result.layout.overflows equals `full.result.layout.overflows`
- Verify fragments mappings and hit index
   - Expected: full.result.epoch equals `1`
   - Expected: incremental.result.epoch equals `2`
   - Expected: incremental.result.hit_regions.len() equals `browser.raw_boxes.bx.len()`
   - Expected: incremental.result.hit_regions[0].generation equals `7`
   - Expected: incremental.result.hit_regions[0].epoch equals `2`
   - Expected: incremental.result.hit_regions[0].structural_id equals `1`
   - Expected: incremental.result.hit_regions[0].dom_route_id equals `0`
   - Expected: incremental.result.layout.mappings[0].kind equals `LayoutOf`
   - Expected: incremental.result.hit_mappings[0].kind equals `HitRegionOf`
- Restrict viewport invalidation to changed geometry
   - Expected: web_layout_dirty_frontier([viewport_change]).invalidated_ids equals `[flex_id]`
   - Expected: stale.result.stale is true
   - Expected: stale.result.fault equals `stale-dom-generation`
   - Expected: unsupported.result.fault equals `unsupported-profile:mystery`
   - Expected: unsupported.result.epoch equals `0`
   - Expected: exhausted.result.fault equals `epoch-exhausted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 132 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves the browser oracle through incremental framework execution")
step("Capture the CPU layout oracle")
val browser = simple_web_layout_render_html_draw_ir_result(
    "<div style='display:grid;width:200px'><span>A</span></div>" +
    "<div style='display:flex;width:200px'><span>B</span></div>",
    640,
    480
)
val execution = layout_execution_profile(
    "serial_cpu", 50, 0, 0, 0, 0, 0, 0, 0
)
val adapted = web_layout_adapt_cpu_oracle(browser, 7, execution, 4)
expect(adapted.fault).to_equal("")
expect(adapted.snapshot.nodes.len()).to_equal(browser.raw_boxes.bx.len())
expect(adapted.snapshot.text_requests.len()).to_be_greater_than(0)
expect(adapted.snapshot.text_results.len()).to_equal(adapted.snapshot.text_requests.len())
var index: i64 = 0
while index < adapted.snapshot.nodes.len():
    val node = adapted.snapshot.nodes[index]
    expect(node.id).to_equal(index + 1)
    expect(node.arena_index).to_equal(index)
    expect(node.dom_route_id).to_equal(index)
    expect(adapted.snapshot.oracle_boxes[index].x).to_equal(browser.raw_boxes.bx[index] as i64)
    expect(adapted.snapshot.oracle_boxes[index].y).to_equal(browser.raw_boxes.by[index] as i64)
    expect(adapted.snapshot.oracle_boxes[index].width).to_equal(browser.raw_boxes.bw[index] as i64)
    expect(adapted.snapshot.oracle_boxes[index].height).to_equal(browser.raw_boxes.bh[index] as i64)
    index = index + 1

step("Classify browser layout islands")
var flex_id: i64 = 0
for node in adapted.snapshot.nodes:
    if node.profile_id == "flex":
        flex_id = node.id
expect(flex_id).to_be_greater_than(0)
val frontier = web_layout_dirty_frontier([system_change(flex_id, flex_id)])
expect(frontier.invalidated_ids).to_equal([flex_id])

step("Apply the invalidated frontier")
val manager = web_layout_manager(7)
val full = web_layout_run_full(
    manager, adapted.snapshot, web_layout_dirty_frontier([])
)
val incremental = web_layout_run_incremental(
    full.manager, adapted.snapshot, frontier
)
expect(full.result.fault).to_equal("")
expect(incremental.result.fault).to_equal("")
expect(full.result.layout.fragments).to_equal(adapted.snapshot.oracle_fragments)
expect(full.result.layout.line_boxes).to_equal(adapted.snapshot.oracle_line_boxes)
expect(full.result.layout.overflows).to_equal(adapted.snapshot.oracle_overflows)
expect(incremental.result.layout.boxes).to_equal(full.result.layout.boxes)
expect(incremental.result.layout.fragments).to_equal(full.result.layout.fragments)
expect(incremental.result.layout.line_boxes).to_equal(full.result.layout.line_boxes)
expect(incremental.result.layout.overflows).to_equal(full.result.layout.overflows)
expect(incremental.result.layout.receipt.visited_island_ids.len()).to_be_greater_than(0)
expect(incremental.result.layout.receipt.visited_island_ids.len()).to_be_less_than(
    full.result.layout.islands.len()
)

step("Verify fragments mappings and hit index")
expect(full.result.epoch).to_equal(1)
expect(incremental.result.epoch).to_equal(2)
expect(incremental.result.hit_regions.len()).to_equal(browser.raw_boxes.bx.len())
expect(incremental.result.hit_regions[0].generation).to_equal(7)
expect(incremental.result.hit_regions[0].epoch).to_equal(2)
expect(incremental.result.hit_regions[0].structural_id).to_equal(1)
expect(incremental.result.hit_regions[0].dom_route_id).to_equal(0)
expect(incremental.result.layout.mappings[0].kind).to_equal("LayoutOf")
expect(incremental.result.hit_mappings.len()).to_equal(
    incremental.result.hit_regions.len()
)
expect(incremental.result.hit_mappings[0].kind).to_equal("HitRegionOf")
expect(incremental.result.hit_mappings[0].target_id).to_equal(
    incremental.result.hit_regions[0].dom_route_id
)

step("Restrict viewport invalidation to changed geometry")
val viewport_change = web_layout_change(
    WebLayoutMutationKind.Viewport,
    StyleDifference.NoChange,
    0, 0, [], [], [], [], [], [], [flex_id]
)
expect(web_layout_dirty_frontier([viewport_change]).invalidated_ids).to_equal([flex_id])

val stale = web_layout_run_full(
    web_layout_manager(8), adapted.snapshot, web_layout_dirty_frontier([])
)
expect(stale.result.stale).to_equal(true)
expect(stale.result.fault).to_equal("stale-dom-generation")

val seed = adapted.snapshot.nodes[0]
val unsupported_node = WebLayoutNodeSnapshot(
    id: seed.id,
    arena_index: seed.arena_index,
    dom_route_id: seed.dom_route_id,
    parent_id: seed.parent_id,
    tag: seed.tag,
    profile_id: "mystery",
    formatting_boundary: seed.formatting_boundary,
    layout_contained: seed.layout_contained,
    style: seed.style,
    text_content: seed.text_content,
    font_family: seed.font_family,
    font_size: seed.font_size,
    language: seed.language,
    text_metrics: seed.text_metrics,
    semantics: seed.semantics,
    estimated_work: seed.estimated_work,
    text_measure_required: seed.text_measure_required
)
val unsupported_snapshot = web_layout_snapshot(
    7, adapted.snapshot.viewport_fingerprint, [unsupported_node],
    [], execution, 4,
    adapted.snapshot.viewport_width,
    adapted.snapshot.viewport_height,
    adapted.snapshot.grid_tracks,
    [adapted.snapshot.oracle_boxes[0]]
)
val unsupported = web_layout_run_full(
    web_layout_manager(7), unsupported_snapshot,
    web_layout_dirty_frontier([])
)
expect(unsupported.result.fault).to_equal("unsupported-profile:mystery")
expect(unsupported.result.epoch).to_equal(0)

val exhausted = web_layout_run_full(
    WebLayoutManager(generation: 7, epoch: WEB_LAYOUT_MAX_EPOCH),
    adapted.snapshot,
    web_layout_dirty_frontier([])
)
expect(exhausted.result.fault).to_equal("epoch-exhausted")
```

</details>

#### preserves wrapped lines fragments and overflow extents exactly

- preserves wrapped lines fragments and overflow extents exactly
- Capture wrapped text and clipped overflow from the CPU oracle
   - Expected: adapted.fault equals ``
   - Expected: line.box.width equals `exact_width`
   - Expected: clipped_overflow_found is true
- Run the framework with the exact oracle artifacts
   - Expected: full.result.fault equals ``
   - Expected: full.result.layout.fragments equals `adapted.snapshot.oracle_fragments`
   - Expected: full.result.layout.line_boxes equals `adapted.snapshot.oracle_line_boxes`
   - Expected: full.result.layout.overflows equals `adapted.snapshot.oracle_overflows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves wrapped lines fragments and overflow extents exactly")
step("Capture wrapped text and clipped overflow from the CPU oracle")
val browser = simple_web_layout_render_html_draw_ir_result(
    "<div style='width:48px;overflow:hidden'>alpha beta gamma delta</div>" +
    "<div style='width:40px;overflow:hidden'><div style='width:120px;height:12px'></div></div>",
    320,
    240
)
val execution = layout_execution_profile(
    "serial_cpu", 50, 0, 0, 0, 0, 0, 0, 0
)
val adapted = web_layout_adapt_cpu_oracle(browser, 11, execution, 4)
expect(adapted.fault).to_equal("")

var wrapped_node_id: i64 = 0
var wrapped_line_count: i64 = 0
for node in adapted.snapshot.nodes:
    if node.tag == "#text":
        var node_line_count: i64 = 0
        for line in adapted.snapshot.oracle_line_boxes:
            if line.node_id == node.id:
                node_line_count = node_line_count + 1
                var exact_width: i64 = 0
                var advance_index = line.text_start
                while advance_index < line.text_end:
                    exact_width = exact_width + node.text_metrics.advances[advance_index]
                    advance_index = advance_index + 1
                expect(line.box.width).to_equal(exact_width)
        if node_line_count > 1:
            wrapped_node_id = node.id
            wrapped_line_count = node_line_count
expect(wrapped_node_id).to_be_greater_than(0)
expect(wrapped_line_count).to_be_greater_than(1)

var clipped_overflow_found = false
for overflow in adapted.snapshot.oracle_overflows:
    if (overflow.scroll_width > overflow.clip_box.width or
        overflow.scroll_height > overflow.clip_box.height):
        clipped_overflow_found = true
expect(clipped_overflow_found).to_equal(true)

step("Run the framework with the exact oracle artifacts")
val full = web_layout_run_full(
    web_layout_manager(11),
    adapted.snapshot,
    web_layout_dirty_frontier([])
)
expect(full.result.fault).to_equal("")
expect(full.result.layout.fragments).to_equal(adapted.snapshot.oracle_fragments)
expect(full.result.layout.line_boxes).to_equal(adapted.snapshot.oracle_line_boxes)
expect(full.result.layout.overflows).to_equal(adapted.snapshot.oracle_overflows)
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
- `REQ-WLM-001..REQ-WLM-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d206097f478e08da62e264f38509fdba121836d6eaf093cace055715194292f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d206097f478e08da62e264f38509fdba121836d6eaf093cace055715194292f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d206097f478e08da62e264f38509fdba121836d6eaf093cace055715194292f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/app/web_browser/feature/web_layout_manager_spec.spl
mirror: doc/06_spec/03_system/app/web_browser/feature/web_layout_manager_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/web_browser/feature/web_layout_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/web_browser/feature/web_layout_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/web_browser/feature/web_layout_manager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/web_browser/feature/web_layout_manager_spec.spl:42:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'pre-rejects complex-script GPU line breaking before submission' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/app/web_browser/feature/web_layout_manager_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the browser oracle through incremental framework execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/web_browser/feature/web_layout_manager_spec.spl:203:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves wrapped lines fragments and overflow extents exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
