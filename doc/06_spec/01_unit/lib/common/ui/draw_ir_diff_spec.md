# Draw Ir Diff Specification

> Tests covering Draw IR baseline diff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Diff Specification

## Scenarios

### Draw IR baseline diff

#### reports geometry style color border and text-bound deltas by stable id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports geometry style color border and text-bound deltas by stable id
   - Expected: report.node_count equals `2`
   - Expected: report.changed_count equals `2`
   - Expected: report.diffs[0].component_id equals `box`
   - Expected: report.diffs[0].dx equals `5`
   - Expected: report.diffs[0].dwidth equals `20`
   - Expected: report.diffs[0].color_changed is true
   - Expected: report.diffs[0].style_changed is true
   - Expected: report.diffs[0].border_changed is true
   - Expected: report.diffs[1].text_changed is true
   - Expected: report.diffs[1].text_bounds_changed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports geometry style color border and text-bound deltas by stable id")
val baseline = draw_ir_composition("baseline", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_box_with_style(
            "box",
            10,
            20,
            100,
            40,
            1u32,
            draw_ir_rect_bounds(10, 20, 100, 40),
            draw_ir_rect_bounds(12, 22, 96, 36),
            draw_ir_rect_bounds(10, 20, 100, 40),
            draw_ir_rect_bounds(0, 0, 200, 100),
            [draw_ir_style_prop("fill", "blue")]
        ),
        draw_ir_text("label", 20, 30, "Old", 2u32)
    ])
])
val current = draw_ir_composition("current", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_box_with_style(
            "box",
            15,
            25,
            120,
            50,
            3u32,
            draw_ir_rect_bounds(15, 25, 120, 50),
            draw_ir_rect_bounds(17, 27, 116, 46),
            draw_ir_rect_bounds(15, 25, 120, 50),
            draw_ir_rect_bounds(0, 0, 200, 100),
            [draw_ir_style_prop("fill", "red")]
        ),
        draw_ir_text("label", 22, 33, "New", 2u32)
    ])
])

val report = draw_ir_diff_compositions(baseline, current)

expect(report.node_count).to_equal(2)
expect(report.changed_count).to_equal(2)
expect(report.diffs[0].component_id).to_equal("box")
expect(report.diffs[0].dx).to_equal(5)
expect(report.diffs[0].dwidth).to_equal(20)
expect(report.diffs[0].color_changed).to_equal(true)
expect(report.diffs[0].style_changed).to_equal(true)
expect(report.diffs[0].border_changed).to_equal(true)
expect(report.diffs[1].text_changed).to_equal(true)
expect(report.diffs[1].text_bounds_changed).to_equal(true)
```

</details>

#### reports added and removed nodes

- reports added and removed nodes
   - Expected: report.added_count equals `1`
   - Expected: report.removed_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports added and removed nodes")
val baseline = draw_ir_composition("baseline", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_text("removed", 5, 6, "Gone", 1u32)
    ])
])
val current = draw_ir_composition("current", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_text("added", 7, 8, "New", 1u32)
    ])
])

val report = draw_ir_diff_compositions(baseline, current)
val json = draw_ir_diff_report_to_json(report)

expect(report.added_count).to_equal(1)
expect(report.removed_count).to_equal(1)
expect(json).to_contain("\"state\":\"added\"")
expect(json).to_contain("\"state\":\"removed\"")
```

</details>

#### reports shaped glyph-run-only changes

- reports shaped glyph-run-only changes
   - Expected: report.changed_count equals `1`
   - Expected: report.diffs[0].state equals `changed`
   - Expected: report.diffs[0].text_changed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports shaped glyph-run-only changes")
val baseline = draw_ir_composition("baseline", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_text_shaped_font(
            "arabic", 4, 5, "اب", 0xffffffffu32, "Noto Sans Arabic",
            "sha256=test", [8, 12], 20, 32, 32,
            draw_ir_glyph_run_payload([288u32, 85u32], [3, 0], [2, 0], [1, 0], true)
        )
    ])
])
val changed_payloads = [
    draw_ir_glyph_run_payload([999u32, 85u32], [3, 0], [2, 0], [1, 0], true),
    draw_ir_glyph_run_payload([288u32, 85u32], [4, 0], [2, 0], [1, 0], true),
    draw_ir_glyph_run_payload([288u32, 85u32], [3, 0], [3, 0], [1, 0], true),
    draw_ir_glyph_run_payload([288u32, 85u32], [3, 0], [2, 0], [0, 0], true),
    draw_ir_glyph_run_payload([288u32, 85u32], [3, 0], [2, 0], [1, 0], false),
    draw_ir_glyph_run_payload([288u32, 85u32], [3], [2, 0], [1, 0], true)
]
for changed_payload in changed_payloads:
    val current = draw_ir_composition("current", "scene", DRAW_IR_BACKEND_CPU, [
        draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
            draw_ir_text_shaped_font(
                "arabic", 4, 5, "اب", 0xffffffffu32, "Noto Sans Arabic",
                "sha256=test", [8, 12], 20, 32, 32, changed_payload
            )
        ])
    ])
    val report = draw_ir_diff_compositions(baseline, current)
    expect(report.changed_count).to_equal(1)
    expect(report.diffs[0].state).to_equal("changed")
    expect(report.diffs[0].text_changed).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_diff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Draw IR baseline diff.
- Draw IR baseline diff

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `066189aa767b8affe6f1cf2fb25926b19b8ce15cefc479e1c565a11fb0e5063e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `066189aa767b8affe6f1cf2fb25926b19b8ce15cefc479e1c565a11fb0e5063e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `066189aa767b8affe6f1cf2fb25926b19b8ce15cefc479e1c565a11fb0e5063e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/draw_ir_diff_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/draw_ir_diff_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/draw_ir_diff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/draw_ir_diff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/draw_ir_diff_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/draw_ir_diff_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports geometry style color border and text-bound deltas by stable id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_diff_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports added and removed nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_diff_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports shaped glyph-run-only changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
