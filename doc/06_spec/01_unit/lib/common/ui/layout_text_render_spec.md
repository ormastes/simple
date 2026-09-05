# Layout Text Render Specification

> Tests covering layout_text_render.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layout Text Render Specification

## Scenarios

### layout_text_render

#### renders a snapshot as a stable indented outline

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders a snapshot as a stable indented outline
   - Expected: layout_tree_to_text(snapshot) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a snapshot as a stable indented outline")
val snapshot = _snapshot([
    _node("root", "panel", "", 0, 0, 100, 60, ["main/a", "main/b"]),
    _node("a", "button", "OK", 10, 30, 40, 20, []),
    _node("b", "label", "Hello", 10, 5, 40, 10, [])
])
val expected = "panel #root [0,0 100x60] \"\"\n" +
    "  button #a [10,30 40x20] \"OK\"\n" +
    "  label #b [10,5 40x10] \"Hello\""
expect(layout_tree_to_text(snapshot)).to_equal(expected)
```

</details>

#### orders multiple roots by (y, x) and truncates long content

- orders multiple roots by (y, x) and truncates long content
   - Expected: layout_tree_to_text(snapshot) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("orders multiple roots by (y, x) and truncates long content")
val long_text = "0123456789012345678901234567890123456789XYZ"
val snapshot = _snapshot([
    _node("low", "panel", "", 0, 50, 10, 10, []),
    _node("high", "label", long_text, 0, 0, 10, 10, [])
])
val expected = "label #high [0,0 10x10] \"0123456789012345678901234567890123456789...\"\n" +
    "panel #low [0,50 10x10] \"\""
expect(layout_tree_to_text(snapshot)).to_equal(expected)
```

</details>

#### renders draw cmds one normalized line each

- renders draw cmds one normalized line each
   - Expected: draw_cmds_to_text(cmds) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders draw cmds one normalized line each")
val cmds = [
    _rect("bg", 0, 0, 100, 50),
    DrawCmd(kind: "text", widget_id: "t", x: 5, y: 25, w: 0, h: 0, color: 0xFFE0E0E0u32, label: "Hi", size: 7)
]
val expected = "rect #bg [0,0 100x50] color=#ff112233 \"\" size=0\n" +
    "text #t [5,25 0x0] color=#ffe0e0e0 \"Hi\" size=7"
expect(draw_cmds_to_text(cmds)).to_equal(expected)
```

</details>

#### paints boxes onto an ascii grid with topmost overlap winning

- paints boxes onto an ascii grid with topmost overlap winning
   - Expected: layout_grid_to_text(cmds, 4, 2) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("paints boxes onto an ascii grid with topmost overlap winning")
# World 100x40. A fills all; B covers the right half on top.
val cmds = [
    _rect("a", 0, 0, 100, 40),
    _rect("b", 50, 0, 50, 40)
]
val expected = "AABB\nAABB"
expect(layout_grid_to_text(cmds, 4, 2)).to_equal(expected)
```

</details>

#### grid skips zero-area boxes and leaves empty cells dotted

- grid skips zero-area boxes and leaves empty cells dotted
   - Expected: layout_grid_to_text(cmds, 4, 2) equals `AA..\n....`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grid skips zero-area boxes and leaves empty cells dotted")
val cmds = [
    _rect("a", 0, 0, 50, 20),
    DrawCmd(kind: "text", widget_id: "t", x: 90, y: 30, w: 0, h: 0, color: 0u32, label: "x", size: 7)
]
# World becomes 90x30 from the text cmd's position (max extent),
# box A covers x 0..50 of 90 => cols 0..1 of 4, y 0..20 of 30 => row 0 of 2.
expect(layout_grid_to_text(cmds, 4, 2)).to_equal("AA..\n....")
```

</details>

#### diff of identical renderings is empty

- diff of identical renderings is empty
   - Expected: layout_text_diff(a, a) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diff of identical renderings is empty")
val a = "line1\nline2"
expect(layout_text_diff(a, a)).to_equal("")
```

</details>

#### diff reports a moved box as a changed line with counts

- diff reports a moved box as a changed line with counts
   - Expected: layout_text_diff(before, after) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diff reports a moved box as a changed line with counts")
val before = "rect #a [0,0 10x10]\nrect #b [0,20 10x10]"
val after = "rect #a [0,0 10x10]\nrect #b [5,20 10x10]"
val expected = "diff: -1 +1\n" +
    "- rect #b [0,20 10x10]\n" +
    "+ rect #b [5,20 10x10]"
expect(layout_text_diff(before, after)).to_equal(expected)
```

</details>

#### diff reports pure additions and removals

- diff reports pure additions and removals
   - Expected: layout_text_diff("a\nb", "a\nb\nc") equals `diff: -0 +1\n+ c`
   - Expected: layout_text_diff("a\nb\nc", "a\nc") equals `diff: -1 +0\n- b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diff reports pure additions and removals")
expect(layout_text_diff("a\nb", "a\nb\nc")).to_equal("diff: -0 +1\n+ c")
expect(layout_text_diff("a\nb\nc", "a\nc")).to_equal("diff: -1 +0\n- b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/layout_text_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering layout_text_render.
- layout_text_render

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `851e3c96af416fe0f6b70655fd0b5328c878cb493f5c1f80b6599fcf0ef0e0b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `851e3c96af416fe0f6b70655fd0b5328c878cb493f5c1f80b6599fcf0ef0e0b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `851e3c96af416fe0f6b70655fd0b5328c878cb493f5c1f80b6599fcf0ef0e0b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/layout_text_render_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/layout_text_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/layout_text_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/layout_text_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/layout_text_render_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a snapshot as a stable indented outline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/layout_text_render_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'orders multiple roots by (y, x) and truncates long content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/layout_text_render_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders draw cmds one normalized line each' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
