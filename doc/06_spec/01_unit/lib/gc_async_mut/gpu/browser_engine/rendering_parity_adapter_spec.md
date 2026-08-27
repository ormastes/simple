# Rendering Parity Adapter Specification

> Tests covering Simple Web rendering parity observation adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rendering Parity Adapter Specification

## Scenarios

### Simple Web rendering parity observation adapter

#### observes production DOM style layout and Draw IR in one result

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- observes production DOM style layout and Draw IR in one result
   - Expected: SIMPLE_WEB_PARITY_CONVERTER equals `simple-web-stage-v1`
   - Expected: records.len() equals `4`
   - Expected: records[0].stage equals `dom`
   - Expected: records[3].stage equals `paint`
   - Expected: records[1].input_checksum equals `records[0].output_checksum`
   - Expected: records[3].ordinal equals `3`
   - Expected: records[0].payload equals `observed.dom_payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("observes production DOM style layout and Draw IR in one result")
val html = "<style>body{margin:0}#card{width:12px;height:7px;background:#123456}</style><div id='card'>A:B;C</div>"
val observed = simple_web_rendering_parity_observe(html, 32, 24)
expect(SIMPLE_WEB_PARITY_CONVERTER).to_equal("simple-web-stage-v1")
expect(observed.node_count).to_be_greater_than(2)
expect(observed.command_count).to_be_greater_than(0)
expect(observed.dom_payload).to_start_with("schema=dom-v1")
expect(observed.dom_payload).to_contain("id(4:card)")
expect(observed.dom_payload).to_contain("5:A:B;C")
expect(observed.style_payload).to_start_with("schema=style-v1")
expect(observed.layout_payload).to_start_with("schema=layout-v1")
expect(observed.paint_payload).to_start_with("schema=paint-v1")
expect(observed.degraded).to_be(false)

val records = simple_web_rendering_parity_stage_records("card", "cpu", html, 32, 24).unwrap()
expect(records.len()).to_equal(4)
expect(records[0].stage).to_equal("dom")
expect(records[3].stage).to_equal("paint")
expect(records[1].input_checksum).to_equal(records[0].output_checksum)
expect(records[3].ordinal).to_equal(3)
expect(records[0].payload).to_equal(observed.dom_payload)
```

</details>

#### is deterministic for identical production input

- is deterministic for identical production input
   - Expected: second.dom_payload equals `first.dom_payload`
   - Expected: second.style_payload equals `first.style_payload`
   - Expected: second.layout_payload equals `first.layout_payload`
   - Expected: second.paint_payload equals `first.paint_payload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic for identical production input")
val html = "<main><p id='same'>stable</p></main>"
val first = simple_web_rendering_parity_observe(html, 80, 40)
val second = simple_web_rendering_parity_observe(html, 80, 40)
expect(second.dom_payload).to_equal(first.dom_payload)
expect(second.style_payload).to_equal(first.style_payload)
expect(second.layout_payload).to_equal(first.layout_payload)
expect(second.paint_payload).to_equal(first.paint_payload)
```

</details>

#### changes paint payload when only semantic clip geometry changes

- changes paint payload when only semantic clip geometry changes


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("changes paint payload when only semantic clip geometry changes")
val first_command = draw_ir_box_with_style(
    "box", 1, 2, 3, 4, 0xff112233u32,
    draw_ir_rect_bounds(1, 2, 3, 4),
    draw_ir_rect_bounds(1, 2, 3, 4),
    draw_ir_rect_bounds(1, 2, 3, 4),
    draw_ir_rect_bounds(0, 0, 8, 8), []
)
val second_command = draw_ir_box_with_style(
    "box", 1, 2, 3, 4, 0xff112233u32,
    draw_ir_rect_bounds(1, 2, 3, 4),
    draw_ir_rect_bounds(1, 2, 3, 4),
    draw_ir_rect_bounds(1, 2, 3, 4),
    draw_ir_rect_bounds(0, 0, 7, 8), []
)
val embedding = draw_ir_embedding_config(
    "surface", "component", 0, 0, 8, 8, 0, 1000, true
)
val first = draw_ir_composition(
    "same", "scene", DRAW_IR_BACKEND_CPU,
    [draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, embedding, [first_command])]
)
val second = draw_ir_composition(
    "same", "scene", DRAW_IR_BACKEND_CPU,
    [draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, embedding, [second_command])]
)
val first_payload = simple_web_rendering_parity_paint_payload(first)
val second_payload = simple_web_rendering_parity_paint_payload(second)
expect(first_payload == second_payload).to_be(false)
expect(first_payload).to_contain("clip_width=8")
expect(second_payload).to_contain("clip_width=7")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Web rendering parity observation adapter.
- Simple Web rendering parity observation adapter

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

- Canonical SPipe generation for source `2cdb05159e1d620c1063506ee58a9037f5541eac456073281070c26c47dd27d3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2cdb05159e1d620c1063506ee58a9037f5541eac456073281070c26c47dd27d3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2cdb05159e1d620c1063506ee58a9037f5541eac456073281070c26c47dd27d3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'observes production DOM style layout and Draw IR in one result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is deterministic for identical production input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/rendering_parity_adapter_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'changes paint payload when only semantic clip geometry changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
