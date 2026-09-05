# Tui Facade Specification

> Tests covering nogc_async_mut tui facades.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Facade Specification

## Scenarios

### nogc_async_mut tui facades

#### re-exports pure TUI style, widget, and layout helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports pure TUI style, widget, and layout helpers
   - Expected: render_line(make_styled_line("err", style)) contains `err`
   - Expected: render_line(make_plain_line("plain")) equals `plain`
   - Expected: rgb_style.fg_rgb.g equals `2`
   - Expected: fg_style(COLOR_RED).fg equals `COLOR_RED`
   - Expected: bold_style().bold is true
   - Expected: inner.x equals `4`
   - Expected: inner.width equals `74`
   - Expected: rect_area(area) equals `1920`
   - Expected: rect_right(area) equals `80`
   - Expected: rect_bottom(area) equals `24`
   - Expected: rect_contains(area, 10, 10) is true
   - Expected: pad_or_truncate("abc", 5) equals `abc  `
   - Expected: pad_or_truncate("abcdef", 3) equals `abc`
   - Expected: buf.lines[1].segments[0].content equals `row`
   - Expected: split_vertical(area, [1, 1]).len() equals `2`
   - Expected: split_horizontal(area, [1, 1])[1].x equals `40`
   - Expected: split_vertical_fixed(area, [5, -1])[1].height equals `19`
   - Expected: split_horizontal_fixed(area, [10, -1])[1].width equals `70`
   - Expected: apply_margin(area, make_margin(1, 2, 3, 4)).x equals `4`
   - Expected: apply_margin(area, make_uniform_margin(2)).width equals `76`
   - Expected: center_rect(area, 20, 10).x equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports pure TUI style, widget, and layout helpers")
val style = make_style(COLOR_RED, COLOR_NONE, true, false, false, false)
expect(render_line(make_styled_line("err", style)).contains("err")).to_equal(true)
expect(render_line(make_plain_line("plain"))).to_equal("plain")
val rgb_style = make_style_rgb(RgbColor(r: 1, g: 2, b: 3), RgbColor(r: 4, g: 5, b: 6), false, false, false, false)
expect(rgb_style.fg_rgb.g).to_equal(2)
expect(fg_style(COLOR_RED).fg).to_equal(COLOR_RED)
expect(bold_style().bold).to_equal(true)

val area = make_rect(0, 0, 80, 24)
val inner = rect_inner(area, 1, 2, 3, 4)
expect(inner.x).to_equal(4)
expect(inner.width).to_equal(74)
expect(rect_area(area)).to_equal(1920)
expect(rect_right(area)).to_equal(80)
expect(rect_bottom(area)).to_equal(24)
expect(rect_contains(area, 10, 10)).to_equal(true)
expect(pad_or_truncate("abc", 5)).to_equal("abc  ")
expect(pad_or_truncate("abcdef", 3)).to_equal("abc")

val buf = buffer_set_line(make_render_buffer(5, 2), 1, make_plain_line("row"))
expect(buf.lines[1].segments[0].content).to_equal("row")

expect(split_vertical(area, [1, 1]).len()).to_equal(2)
expect(split_horizontal(area, [1, 1])[1].x).to_equal(40)
expect(split_vertical_fixed(area, [5, -1])[1].height).to_equal(19)
expect(split_horizontal_fixed(area, [10, -1])[1].width).to_equal(70)
expect(apply_margin(area, make_margin(1, 2, 3, 4)).x).to_equal(4)
expect(apply_margin(area, make_uniform_margin(2)).width).to_equal(76)
expect(center_rect(area, 20, 10).x).to_equal(30)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut tui facades.
- nogc_async_mut tui facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c85422da6038ba01116ff33cf32f43fecb0aeca08acca24d058387a5c8e13b89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c85422da6038ba01116ff33cf32f43fecb0aeca08acca24d058387a5c8e13b89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c85422da6038ba01116ff33cf32f43fecb0aeca08acca24d058387a5c8e13b89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports pure TUI style, widget, and layout helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
