# Draw IR Inspection Contract

> Red-phase source-contract coverage for Draw IR Phases 4-6. These scenarios spell out the endpoint, producer-enrichment, and `expect_draw` surfaces before implementation work starts. They are intentionally concrete assertions rather than synthetic fail-only cases.

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
| Updated | 2026-08-26 |
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

#### endpoint family stays named in the implementation plan

- should keep the endpoint family named in the implementation plan
   - Expected: _has(plan, "/api/test/draw-ir") is true
   - Expected: _has(plan, "/api/test/draw-ir?id=") is true
   - Expected: _has(plan, "/api/test/draw-ir/diff") is true
   - Expected: _has(plan, "/api/test/draw-ir/layout?id=") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-001
# @req REQ-SSPEC-SYSTEM
step("should keep the endpoint family named in the implementation plan")
val plan = _read(PLAN_PATH)
expect(_has(plan, "/api/test/draw-ir")).to_equal(true)
expect(_has(plan, "/api/test/draw-ir?id=")).to_equal(true)
expect(_has(plan, "/api/test/draw-ir/diff")).to_equal(true)
expect(_has(plan, "/api/test/draw-ir/layout?id=")).to_equal(true)
```

</details>

#### add concrete draw-ir route handling to ui.test_api

- should add concrete draw-ir route handling to ui.test_api
   - Expected: _has(handler, "/api/test/draw-ir") is true
   - Expected: _has_any2(handler, "draw_ir", "draw-ir") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-001
step("should add concrete draw-ir route handling to ui.test_api")
val handler = _read(UI_TEST_HANDLER_PATH)
expect(_has(handler, "/api/test/draw-ir")).to_equal(true)
expect(_has_any2(handler, "draw_ir", "draw-ir")).to_equal(true)
```

</details>

#### advertise Protocol v2 separately from the v1 API

- should advertise Protocol v2 separately from the v1 API
   - Expected: _has(handler, "X-UI-Protocol-Version") is true
   - Expected: _has_any2(handler, "Protocol v2", "\"2\"") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-001
step("should advertise Protocol v2 separately from the v1 API")
val handler = _read(UI_TEST_HANDLER_PATH)
expect(_has(handler, "X-UI-Protocol-Version")).to_equal(true)
expect(_has_any2(handler, "Protocol v2", "\"2\"")).to_equal(true)
```

</details>

#### guard draw-ir inspection behind an explicit capability

- should guard draw-ir inspection behind an explicit capability
   - Expected: _has_any2(handler, "capability", "CAPABILITY") is true
   - Expected: _has_any2(handler, "draw_ir", "draw-ir") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-001
step("should guard draw-ir inspection behind an explicit capability")
val handler = _read(UI_TEST_HANDLER_PATH)
expect(_has_any2(handler, "capability", "CAPABILITY")).to_equal(true)
expect(_has_any2(handler, "draw_ir", "draw-ir")).to_equal(true)
```

</details>

### REQ-DRAW-INSPECT-002: Producer enrichment

#### WM Draw IR enriched with hit and clip rectangles

- should enrich WM Draw IR with hit and clip rectangles
   - Expected: _has(source, "hit_rect") is true
   - Expected: _has(source, "clip_rect") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-002
step("should enrich WM Draw IR with hit and clip rectangles")
val source = _read(WM_DRAW_IR_PATH)
expect(_has(source, "hit_rect")).to_equal(true)
expect(_has(source, "clip_rect")).to_equal(true)
```

</details>

#### WM Draw IR enriched with z-index style

- should enrich WM Draw IR with z-index style
   - Expected: _has_any2(source, "z-index", "z_index") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-002
step("should enrich WM Draw IR with z-index style")
val source = _read(WM_DRAW_IR_PATH)
expect(_has_any2(source, "z-index", "z_index")).to_equal(true)
```

</details>

#### web Draw IR enriched with computed style and box rectangles

- should enrich web Draw IR with computed style and box rectangles
   - Expected: _has(source, "computed_style") is true
   - Expected: _has(source, "content_rect") is true
   - Expected: _has(source, "hit_rect") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-002
step("should enrich web Draw IR with computed style and box rectangles")
val source = _read(WEB_LAYOUT_PATH) + _read(WEB_LAYOUT_CORE_PATH) + _read(WEB_LAYOUT_PAINT_PATH)
expect(_has(source, "computed_style")).to_equal(true)
expect(_has(source, "content_rect")).to_equal(true)
expect(_has(source, "hit_rect")).to_equal(true)
```

</details>

### REQ-DRAW-INSPECT-003: expect_draw helper

#### expose expect_draw from the UI test helper layer

- should expose expect_draw from the UI test helper layer
   - Expected: _has(source, "expect_draw") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-003
step("should expose expect_draw from the UI test helper layer")
val source = _read(UI_TEST_DRIVER_PATH)
expect(_has(source, "expect_draw")).to_equal(true)
```

</details>

#### keep expect_draw inside normal std.spec scenarios

- should keep expect_draw inside normal std.spec scenarios
   - Expected: _has(plan, "inside normal SPipe specs") is true
   - Expected: _has(plan, "use std.spec") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-003
step("should keep expect_draw inside normal std.spec scenarios")
val plan = _read(PLAN_PATH)
expect(_has(plan, "inside normal SPipe specs")).to_equal(true)
expect(_has(plan, "use std.spec")).to_equal(true)
```

</details>

#### cover geometry, hit rect, css, parent, and kind assertions

- should cover geometry, hit rect, css, parent, and kind assertions
   - Expected: _has(plan, "geometry") is true
   - Expected: _has(plan, "hit_rect") is true
   - Expected: _has(plan, "css") is true
   - Expected: _has(plan, "parent") is true
   - Expected: _has(plan, "kind") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-003
step("should cover geometry, hit rect, css, parent, and kind assertions")
val plan = _read(PLAN_PATH)
expect(_has(plan, "geometry")).to_equal(true)
expect(_has(plan, "hit_rect")).to_equal(true)
expect(_has(plan, "css")).to_equal(true)
expect(_has(plan, "parent")).to_equal(true)
expect(_has(plan, "kind")).to_equal(true)
```

</details>

### REQ-DRAW-INSPECT-004: v1 compatibility guardrails

#### document Protocol v2 without replacing v1 element endpoints

- should document Protocol v2 without replacing v1 element endpoints
   - Expected: _has(contract, "Protocol v2") is true
   - Expected: _has(contract, "/api/test/draw-ir") is true
   - Expected: _has(contract, "/api/test/elements") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-004
step("should document Protocol v2 without replacing v1 element endpoints")
val contract = _read(SHARED_CONTRACT_PATH)
expect(_has(contract, "Protocol v2")).to_equal(true)
expect(_has(contract, "/api/test/draw-ir")).to_equal(true)
expect(_has(contract, "/api/test/elements")).to_equal(true)
```

</details>

#### reject empty source as satisfying the endpoint contract

- should reject empty source as satisfying the endpoint contract
   - Expected: _has("", "/api/test/draw-ir") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-004
step("should reject empty source as satisfying the endpoint contract")
expect(_has("", "/api/test/draw-ir")).to_equal(false)
```

</details>

#### detect a synthetic Protocol v2 header marker

- should detect a synthetic Protocol v2 header marker
   - Expected: _has(sample, "X-UI-Protocol-Version") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-DRAW-INSPECT-004
step("should detect a synthetic Protocol v2 header marker")
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

- **Plan:** `doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md`
- **Design:** `doc/04_architecture/ui/ui_test_architecture.md`
- **Research:** `doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-DRAW-INSPECT-001`
- `REQ-DRAW-INSPECT-002`
- `REQ-DRAW-INSPECT-003`
- `REQ-DRAW-INSPECT-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e760f382246267915a3659a052df06828acc460b2b792222d7c01c4958d2880`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e760f382246267915a3659a052df06828acc460b2b792222d7c01c4958d2880`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e760f382246267915a3659a052df06828acc460b2b792222d7c01c4958d2880`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl
mirror: doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'endpoint family stays named in the implementation plan' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add concrete draw-ir route handling to ui.test_api' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/ui_test_api/feature/draw_ir_inspection_contract_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advertise Protocol v2 separately from the v1 API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
