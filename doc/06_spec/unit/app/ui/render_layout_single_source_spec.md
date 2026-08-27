# TUI Panel Splitting Has One Home

> As a TUI author I want one place that answers "how do I divide this area into panels", so a fix to the rounding rule reaches every screen instead of only the half that happened to import the right module.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TUI Panel Splitting Has One Home

As a TUI author I want one place that answers "how do I divide this area into panels", so a fix to the rounding rule reaches every screen instead of only the half that happened to import the right module.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/render_layout_single_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

As a TUI author I want one place that answers "how do I divide this area into
panels", so a fix to the rounding rule reaches every screen instead of only the
half that happened to import the right module.

Panel splitting is `std.tui.layout` (`src/lib/nogc_sync_mut/tui/layout.spl`).
`app.ui.render.layout` keeps only what `std.tui.layout` does not offer: the
`LayoutRect` value used by the border renderer, `grid_layout`, and the
ANSI-aware text measurement helpers. It previously carried a second, unreferenced
copy of proportional and fixed splitting; that copy is gone and must not return.

## Examples

`split_vertical(area, [1, 3])` on a 40-row area yields rows of 10 and 30, with
the last part absorbing the rounding remainder. Asking `app.ui.render.layout`
for the same function is a compile error, because it does not define one.

**Traceability:** REQ-UI-LAYOUT-001

## Scenarios

### TUI panel splitting has one home

#### splits an area by ratio with the last part absorbing the remainder

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-UI-LAYOUT-001
```

</details>

#### splits an area horizontally through the same module

- splits an area horizontally through the same module
- divide an 80-column area in a 1:1 ratio
- expect two side-by-side columns that tile the area exactly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits an area horizontally through the same module")
step("divide an 80-column area in a 1:1 ratio")
val cols = split_horizontal(make_rect(0, 0, 80, 40), [1, 1])
step("expect two side-by-side columns that tile the area exactly")
expect(cols.len()).to_be(2)
expect(cols[0].width).to_be(40)
expect(cols[1].width).to_be(40)
expect(cols[0].x + cols[0].width).to_be(cols[1].x)
```

</details>

#### keeps the render layout module free of a second splitting copy

- keeps the render layout module free of a second splitting copy
- read the render layout module from disk
- prove the file was actually read before asserting on its absence
- expect no splitting functions redeclared here


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the render layout module free of a second splitting copy")
step("read the render layout module from disk")
val source = render_layout_source()
step("prove the file was actually read before asserting on its absence")
expect(source.len() > 0).to_be(true)
expect(defines(source, "grid_layout")).to_be(true)
step("expect no splitting functions redeclared here")
expect(defines(source, "split_vertical")).to_be(false)
expect(defines(source, "split_horizontal")).to_be(false)
expect(defines(source, "split_left")).to_be(false)
expect(defines(source, "split_right")).to_be(false)
expect(defines(source, "split_top")).to_be(false)
expect(defines(source, "split_bottom")).to_be(false)
expect(defines(source, "center_in")).to_be(false)
expect(defines(source, "stack_layout")).to_be(false)
expect(defines(source, "center_text")).to_be(false)
```

</details>

#### still offers the grid and measurement helpers its callers import

- still offers the grid and measurement helpers its callers import
- build a 2x2 grid over a 10x4 area
- expect two rows of two cells
- expect ANSI escapes to contribute no visible width


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still offers the grid and measurement helpers its callers import")
step("build a 2x2 grid over a 10x4 area")
val cells = grid_layout(LayoutRect(x: 0, y: 0, width: 10, height: 4), 2, 2, 0)
step("expect two rows of two cells")
expect(cells.len()).to_be(2)
expect(cells[0].len()).to_be(2)
step("expect ANSI escapes to contribute no visible width")
expect(text_width("\u{001b}[31mabc\u{001b}[0m")).to_be(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-UI-LAYOUT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1485bcf08ac18d75745bdcd3dd90c1b6d858b51bfe375befa0fef08414c9777a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1485bcf08ac18d75745bdcd3dd90c1b6d858b51bfe375befa0fef08414c9777a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1485bcf08ac18d75745bdcd3dd90c1b6d858b51bfe375befa0fef08414c9777a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/app/ui/render_layout_single_source_spec.spl
mirror: doc/06_spec/unit/app/ui/render_layout_single_source_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/render_layout_single_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/render_layout_single_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/render_layout_single_source_spec.spl:49:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'splits an area by ratio with the last part absorbing the remainder' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/unit/app/ui/render_layout_single_source_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits an area horizontally through the same module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/render_layout_single_source_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the render layout module free of a second splitting copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/render_layout_single_source_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still offers the grid and measurement helpers its callers import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
