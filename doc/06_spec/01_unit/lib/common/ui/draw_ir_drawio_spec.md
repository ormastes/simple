# Draw Ir Drawio Specification

> Tests covering Draw IR Draw.io mxGraph skin.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Drawio Specification

## Scenarios

### Draw IR Draw.io mxGraph skin

#### imports a Draw.io fixture into Draw IR boxes and edges

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- imports a Draw.io fixture into Draw IR boxes and edges
   - Expected: composition.schema equals `simple-draw-ir-v2`
   - Expected: commands.len() equals `3`
   - Expected: commands[0].kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: commands[0].component_id equals `box-a`
   - Expected: commands[0].parent_id equals `1`
   - Expected: commands[0].x equals `20`
   - Expected: commands[0].y equals `30`
   - Expected: commands[0].width equals `120`
   - Expected: commands[0].height equals `60`
   - Expected: commands[0].computed_style[0].key equals `rounded`
   - Expected: commands[0].computed_style[1].value equals `#dae8fc`
   - Expected: commands[2].kind equals `DRAW_IR_COMMAND_EDGE`
   - Expected: commands[2].edge.source equals `box-a`
   - Expected: commands[2].edge.target equals `box-b`
   - Expected: commands[2].edge.routing equals `DRAW_IR_EDGE_ORTHOGONAL`
   - Expected: commands[2].edge.style[1].key equals `strokeColor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("imports a Draw.io fixture into Draw IR boxes and edges")
val composition = mxgraph_to_draw_ir(_drawio_fixture())
val commands = composition.batches[0].commands

expect(composition.schema).to_equal("simple-draw-ir-v2")
expect(commands.len()).to_equal(3)
expect(commands[0].kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(commands[0].component_id).to_equal("box-a")
expect(commands[0].parent_id).to_equal("1")
expect(commands[0].x).to_equal(20)
expect(commands[0].y).to_equal(30)
expect(commands[0].width).to_equal(120)
expect(commands[0].height).to_equal(60)
expect(commands[0].computed_style[0].key).to_equal("rounded")
expect(commands[0].computed_style[1].value).to_equal("#dae8fc")
expect(commands[2].kind).to_equal(DRAW_IR_COMMAND_EDGE)
expect(commands[2].edge.source).to_equal("box-a")
expect(commands[2].edge.target).to_equal("box-b")
expect(commands[2].edge.routing).to_equal(DRAW_IR_EDGE_ORTHOGONAL)
expect(commands[2].edge.style[1].key).to_equal("strokeColor")
```

</details>

#### exports and re-imports box edge geometry and style identity

- exports and re-imports box edge geometry and style identity
   - Expected: commands.len() equals `3`
   - Expected: commands[0].component_id equals `box-a`
   - Expected: commands[0].x equals `20`
   - Expected: commands[0].width equals `120`
   - Expected: commands[0].computed_style[1].value equals `#dae8fc`
   - Expected: commands[2].component_id equals `edge-a-b`
   - Expected: commands[2].edge.source equals `box-a`
   - Expected: commands[2].edge.target equals `box-b`
   - Expected: commands[2].edge.style[0].value equals `block`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports and re-imports box edge geometry and style identity")
val embedding = draw_ir_embedding_config("surface", "root", 0, 0, 400, 160, 0, 1000, false)
val imported = mxgraph_to_draw_ir(_drawio_fixture())
val composition = draw_ir_composition("diagram", "scene-1", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("diagram-batch", DRAW_IR_BACKEND_CPU, embedding, imported.batches[0].commands)
])

val mxgraph = draw_ir_to_mxgraph(composition)
val reparsed = mxgraph_to_draw_ir(mxgraph)
val commands = reparsed.batches[0].commands

expect(mxgraph).to_contain("<mxGraphModel")
expect(mxgraph).to_contain("id=\"box-a\"")
expect(mxgraph).to_contain("source=\"box-a\" target=\"box-b\" edge=\"1\"")
expect(commands.len()).to_equal(3)
expect(commands[0].component_id).to_equal("box-a")
expect(commands[0].x).to_equal(20)
expect(commands[0].width).to_equal(120)
expect(commands[0].computed_style[1].value).to_equal("#dae8fc")
expect(commands[2].component_id).to_equal("edge-a-b")
expect(commands[2].edge.source).to_equal("box-a")
expect(commands[2].edge.target).to_equal("box-b")
expect(commands[2].edge.style[0].value).to_equal("block")
```

</details>

#### exports hand-built Draw IR edge commands as mxGraph edges

- exports hand-built Draw IR edge commands as mxGraph edges


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports hand-built Draw IR edge commands as mxGraph edges")
val edge = draw_edge(
    "edge-manual",
    "node-a",
    "node-b",
    DRAW_IR_EDGE_ORTHOGONAL,
    [],
    [draw_ir_style_prop("endArrow", "block")]
)
val composition = draw_ir_composition("diagram", "scene-2", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch(
        "manual",
        DRAW_IR_BACKEND_CPU,
        draw_ir_embedding_config("surface", "root", 0, 0, 200, 100, 0, 1000, false),
        [draw_ir_edge_command(edge)]
    )
])

val mxgraph = draw_ir_to_mxgraph(composition)

expect(mxgraph).to_contain("id=\"edge-manual\"")
expect(mxgraph).to_contain("source=\"node-a\"")
expect(mxgraph).to_contain("target=\"node-b\"")
expect(mxgraph).to_contain("edge=\"1\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Draw IR Draw.io mxGraph skin.
- Draw IR Draw.io mxGraph skin

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

- Canonical SPipe generation for source `a7cd390f8939c1991d2376d747581ef3ea930d7b47f5ccd4b020fb26899a5442`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7cd390f8939c1991d2376d747581ef3ea930d7b47f5ccd4b020fb26899a5442`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7cd390f8939c1991d2376d747581ef3ea930d7b47f5ccd4b020fb26899a5442`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/draw_ir_drawio_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/draw_ir_drawio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/draw_ir_drawio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports a Draw.io fixture into Draw IR boxes and edges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports and re-imports box edge geometry and style identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports hand-built Draw IR edge commands as mxGraph edges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
