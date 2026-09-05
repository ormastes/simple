# CSS Grid auto-size item stretch

> This bounded scenario proves that non-replaced Grid items with an automatic block size stretch across one explicit pixel row when effective self-alignment is `normal` or `stretch` and neither block-axis margin is automatic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CSS Grid auto-size item stretch

This bounded scenario proves that non-replaced Grid items with an automatic block size stretch across one explicit pixel row when effective self-alignment is `normal` or `stretch` and neither block-axis margin is automatic.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/grid_auto_item_stretch.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/domain/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This bounded scenario proves that non-replaced Grid items with an automatic
block size stretch across one explicit pixel row when effective self-alignment
is `normal` or `stretch` and neither block-axis margin is automatic.

It covers the canonical production path:

1. authored HTML and CSS;
2. parsed semantic nodes;
3. resolved computed `Style` values;
4. shared layout boxes;
5. canonical `DrawIrComposition` commands;
6. the existing Engine2D software executor;
7. exact framebuffer pixels.

No Grid-specific Draw IR command is introduced.

No private painter or backend path is introduced.

The Web semantic/layout owner remains responsible for used geometry.

Engine2D consumes the resulting canonical composition unchanged.

## Standards contract

CSS Grid item alignment uses the item's `align-self` when it is not `auto`.

Otherwise, the Grid container's `align-items` value is effective.

For the bounded non-replaced items covered here, `normal` behaves as stretch.

Stretch applies only when the authored block size remains automatic.

An authored height therefore remains authoritative.

An automatic top or bottom margin owns block-axis free space and suppresses
stretching.

Physical top and bottom margins are outside the stretched border box.

For `box-sizing:content-box`, physical padding and borders are deducted before
the used CSS height is materialized.

## Syntax

The primary container uses:

```css
display: grid;
grid-template-columns: 4px 4px;
grid-template-rows: 4px;
gap: 0;
align-items: stretch;
```

The children intentionally have backgrounds but no authored height.

The negative controls use:

```css
align-self: start;
margin-top: auto;
height: 2px;
height: 0px;
grid-column: 1 / span 2;
```

The box-model control combines one-pixel top and bottom margins, padding, and
borders inside an eight-pixel explicit row.

The nested control uses `align-items:normal` on its outer Grid and retains an
inner `2px 2px` template after temporary height resolution.

## Examples

The primary fixture is exactly 8 by 4 pixels.

The Grid box is `[0, 0, 8, 4]`.

The red item box is `[0, 0, 4, 4]`.

The blue item box is `[4, 0, 4, 4]`.

Each framebuffer row contains four red pixels and four blue pixels.

All four framebuffer rows are asserted literally.

The expected red command color is `0xFFDC2626`.

The expected blue command color is `0xFF2563EB`.

The expected clip is `[0, 0, 8, 4]`.

The Engine2D skipped-command count is exactly zero.

## Negative controls

The `align-self:start` item remains `[0, 0, 4, 1]`.

The automatic-margin item remains `[4, 0, 4, 1]`.

The explicitly sized item remains `[8, 0, 4, 2]`.

The content-box item becomes `[12, 1, 4, 6]` inside its eight-pixel row.

The authored `height:0px` item remains `[16, 0, 4, 1]`; numeric zero is not
used as a proxy for the `auto` keyword.

The split-cascade item keeps authored `height:0px` and `align-items:stretch`
metadata after an unrelated inline `visibility` declaration forces the full
Style reconstruction path; it remains `[12, 8, 4, 1]`.

Cross-phase final writing modes map authored logical zero sizes onto physical
height consistently: vertical `inline-size:0px` and horizontal
`block-size:0px` both retain `height_px == 0`, `height_auto == false`, and a
one-pixel intrinsic box.

The two-column span remains `[0, 8, 8, 1]` rather than being stretched by the
single-track rule.

The explicitly stretched `video` remains `[8, 8, 4, 1]` because replaced
elements are outside this bounded stretch implementation.

The two-row span remains `[16, 8, 4, 1]` rather than being stretched by the
single-track rule.

These controls prevent a blanket rule that assigns every Grid child the row
height.

## Nested Grid control

The nested Grid is an automatic-height item of a four-pixel outer row.

The outer container uses `align-items:normal`.

The nested Grid stretches to `[0, 0, 4, 4]`.

Its own `grid-template-columns` remains `2px 2px`.

Its own `grid-template-rows` remains `4px`.

Its left child becomes `[0, 0, 2, 4]`.

Its right child becomes `[2, 0, 2, 4]`.

This catches incomplete `Style` clones that discard Grid fields while
materializing a used height.

## Normal versus explicit stretch control

A non-replaced item with `width:2px;aspect-ratio:1/1` and `align-self:normal`
keeps its derived `[0, 0, 2, 2]` size.

The equivalent item with `align-self:stretch` becomes `[4, 0, 2, 4]` because
its authored block size is still automatic.

A Grid container with omitted `align-items` keeps an aspect-ratio-derived item
at `[0, 0, 2, 2]`; the legacy stored default `stretch` is not mistaken for an
authored explicit stretch declaration.

## Claim boundary

Stretching row or column spans remains outside this single-track slice.

Implicit-row stretch is not claimed.

Flexible and intrinsic track sizing is not claimed.

Replaced-element stretch is not claimed.

The fail-closed replaced classification covers `audio`, `button`, `canvas`,
`embed`, `iframe`, `img`, `input`, `meter`, `object`, `progress`, `select`,
`textarea`, and `video`; the executable boundary control uses `video`.

Auto-margin distribution and center/end positioning are not claimed.

Complete CSS Grid or WPT parity is not claimed.

## Requirements

The executable scenario covers REQ-WEB-BROWSER-003,
REQ-WEB-BROWSER-004, and REQ-WEB-BROWSER-021.

It provides semantic, computed-style, layout, Draw IR, and exact-pixel
evidence for the same authored fixture.

## Evidence status

The SSpec contains direct assertions only.

It contains no placeholder pass, boolean wrapper, or silent evidence branch.

Runtime PASS is reported only from an admitted focused execution.

## Scenarios

### REQ-WEB-BROWSER-003/004/021: CSS Grid auto-size stretch

#### should stretch auto-size items through exact Engine2D pixels

**Scenario capture:** artifact after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
# @req REQ-WEB-BROWSER-003
# @req REQ-WEB-BROWSER-004
# @req REQ-WEB-BROWSER-021.
# @req REQ-WEB-BROWSER-003/004/021
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


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/grid_auto_item_stretch.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/domain/simple_web_browser_engine_production_hardening.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WEB-BROWSER-003`
- `REQ-WEB-BROWSER-004`
- `REQ-WEB-BROWSER-021.`
- `REQ-WEB-BROWSER-003/004/021`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8cf1e2483c9331e6d959943dce15aca45cbae7b1b23e6abb2081bdbe53a335c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cf1e2483c9331e6d959943dce15aca45cbae7b1b23e6abb2081bdbe53a335c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cf1e2483c9331e6d959943dce15aca45cbae7b1b23e6abb2081bdbe53a335c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.spl
mirror: doc/06_spec/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=85 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.spl:366:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should stretch auto-size items through exact Engine2D pixels' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/feature/web_platform/css/grid_auto_item_stretch_spec.spl:366:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stretch auto-size items through exact Engine2D pixels' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
