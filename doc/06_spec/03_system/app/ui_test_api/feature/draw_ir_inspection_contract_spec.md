# Draw IR Inspection Contract

> Red-phase source-contract coverage for Draw IR Phases 4-6. These scenarios spell out the endpoint, producer-enrichment, and `expect_draw` surfaces before implementation work starts. They are intentionally concrete assertions rather than synthetic fail-only cases.

<!-- sdn-diagram:id=draw_ir_inspection_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_inspection_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_inspection_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_inspection_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw IR Inspection Contract

Red-phase source-contract coverage for Draw IR Phases 4-6. These scenarios spell out the endpoint, producer-enrichment, and `expect_draw` surfaces before implementation work starts. They are intentionally concrete assertions rather than synthetic fail-only cases.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md |
| Design | doc/04_architecture/ui/ui_test_architecture.md |
| Research | doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md |
| Source | `test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Red-phase source-contract coverage for Draw IR Phases 4-6. These scenarios
spell out the endpoint, producer-enrichment, and `expect_draw` surfaces before
implementation work starts. They are intentionally concrete assertions rather
than synthetic fail-only cases.

**Requirements:** N/A

Requirement IDs in this red-phase spec are local contract labels derived from
the active Draw IR inspection plan.

**Plan:** doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md

**Design:** doc/04_architecture/ui/ui_test_architecture.md

**Research:** doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md

## Syntax

The spec is a source-contract gate. It reads the planned implementation files
and asserts that the named API, protocol, and enrichment markers exist. Before
implementation, execution is expected to fail on the missing markers while
syntax checking remains green.

## Examples

- `/api/test/draw-ir` and related routes must appear in `ui.test_api`.
- `X-UI-Protocol-Version` must advertise the optional Protocol-v2 extension.
- `expect_draw` must live in the UI test helper layer and run inside normal
  `std.spec` scenarios.
- WM and web producers must expose hit/clip/content geometry and computed style
  markers before endpoint behavior is considered implemented.

## Scenarios

### Draw IR inspection contract

### REQ-DRAW-INSPECT-001: Protocol-v2 endpoint surface

#### should keep the endpoint family named in the implementation plan

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(_has(plan, "/api/test/draw-ir")).to_equal(true)
expect(_has(plan, "/api/test/draw-ir?id=")).to_equal(true)
expect(_has(plan, "/api/test/draw-ir/diff")).to_equal(true)
expect(_has(plan, "/api/test/draw-ir/layout?id=")).to_equal(true)
```

</details>

#### should add concrete draw-ir route handling to ui.test_api

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = _read(UI_TEST_HANDLER_PATH)
expect(_has(handler, "/api/test/draw-ir")).to_equal(true)
expect(_has_any2(handler, "draw_ir", "draw-ir")).to_equal(true)
```

</details>

#### should advertise Protocol v2 separately from the v1 API

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = _read(UI_TEST_HANDLER_PATH)
expect(_has(handler, "X-UI-Protocol-Version")).to_equal(true)
expect(_has_any2(handler, "Protocol v2", "\"2\"")).to_equal(true)
```

</details>

#### should guard draw-ir inspection behind an explicit capability

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = _read(UI_TEST_HANDLER_PATH)
expect(_has_any2(handler, "capability", "CAPABILITY")).to_equal(true)
expect(_has_any2(handler, "draw_ir", "draw-ir")).to_equal(true)
```

</details>

### REQ-DRAW-INSPECT-002: Producer enrichment

#### should enrich WM Draw IR with hit and clip rectangles

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(WM_DRAW_IR_PATH)
expect(_has(source, "hit_rect")).to_equal(true)
expect(_has(source, "clip_rect")).to_equal(true)
```

</details>

#### should enrich WM Draw IR with z-index style

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(WM_DRAW_IR_PATH)
expect(_has_any2(source, "z-index", "z_index")).to_equal(true)
```

</details>

#### should enrich web Draw IR with computed style and box rectangles

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(WEB_LAYOUT_PATH)
expect(_has(source, "computed_style")).to_equal(true)
expect(_has(source, "content_rect")).to_equal(true)
expect(_has(source, "hit_rect")).to_equal(true)
```

</details>

### REQ-DRAW-INSPECT-003: expect_draw helper

#### should expose expect_draw from the UI test helper layer

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _read(UI_TEST_DRIVER_PATH)
expect(_has(source, "expect_draw")).to_equal(true)
```

</details>

#### should keep expect_draw inside normal std.spec scenarios

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(_has(plan, "inside normal SPipe specs")).to_equal(true)
expect(_has(plan, "use std.spec")).to_equal(true)
```

</details>

#### should cover geometry, hit rect, css, parent, and kind assertions

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = _read(PLAN_PATH)
expect(_has(plan, "geometry")).to_equal(true)
expect(_has(plan, "hit_rect")).to_equal(true)
expect(_has(plan, "css")).to_equal(true)
expect(_has(plan, "parent")).to_equal(true)
expect(_has(plan, "kind")).to_equal(true)
```

</details>

### REQ-DRAW-INSPECT-004: v1 compatibility guardrails

#### should document Protocol v2 without replacing v1 element endpoints

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = _read(SHARED_CONTRACT_PATH)
expect(_has(contract, "Protocol v2")).to_equal(true)
expect(_has(contract, "/api/test/draw-ir")).to_equal(true)
expect(_has(contract, "/api/test/elements")).to_equal(true)
```

</details>

#### should reject empty source as satisfying the endpoint contract

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has("", "/api/test/draw-ir")).to_equal(false)
```

</details>

#### should detect a synthetic Protocol v2 header marker

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sample = "headers[\"X-UI-Protocol-Version\"] = \"2\""
expect(_has(sample, "X-UI-Protocol-Version")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md](doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md)
- **Design:** [doc/04_architecture/ui/ui_test_architecture.md](doc/04_architecture/ui/ui_test_architecture.md)
- **Research:** [doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md](doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md)


</details>
