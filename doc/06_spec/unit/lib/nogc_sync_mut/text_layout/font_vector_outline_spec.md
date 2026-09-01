# Font Vector Outline Specification

> Tests covering vector font outline rasterization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Font Vector Outline Specification

## Scenarios

### vector font outline rasterization

#### provides a non-empty command stream and positive width for 'A'

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- provides a non-empty command stream and positive width for 'A'


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides a non-empty command stream and positive width for 'A'")
val cmds = vf_glyph_commands(65)
assert_true(cmds.len() > 0)
assert_true(vf_glyph_width(65) > 0)
```

</details>

#### rasterizes 'A' at size 16 with nonzero ink inside the cell

- rasterizes 'A' at size 16 with nonzero ink inside the cell
   - Expected: g.pixels.len() equals `g.width * g.height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasterizes 'A' at size 16 with nonzero ink inside the cell")
val cmds = vf_glyph_commands(65)
val g = rasterize_vector(cmds, 65, 16)
assert_true(g.width > 0)
assert_true(g.height > 0)
assert_true(g.advance > 0)
expect(g.pixels.len()).to_equal(g.width * g.height)
assert_true(ink_count(g.pixels) > 0)
```

</details>

#### grows ink and metrics monotonically from size 16 to 32

- grows ink and metrics monotonically from size 16 to 32


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grows ink and metrics monotonically from size 16 to 32")
val cmds = vf_glyph_commands(65)
val g16 = rasterize_vector(cmds, 65, 16)
val g32 = rasterize_vector(cmds, 65, 32)
assert_true(g32.width > g16.width)
assert_true(g32.height > g16.height)
assert_true(g32.advance > g16.advance)
assert_true(ink_count(g32.pixels) > ink_count(g16.pixels))
```

</details>

#### scales the ink box proportionally within integer rounding

- scales the ink box proportionally within integer rounding


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scales the ink box proportionally within integer rounding")
val cmds = vf_glyph_commands(65)
val g16 = rasterize_vector(cmds, 65, 16)
val g32 = rasterize_vector(cmds, 65, 32)
val bb16 = ink_bbox(g16.pixels, g16.width, g16.height)
val bb32 = ink_bbox(g32.pixels, g32.width, g32.height)
assert_true(bb16[4] > 0)
assert_true(bb32[4] > 0)
val w16 = bb16[2] - bb16[0] + 1
val h16 = bb16[3] - bb16[1] + 1
val w32 = bb32[2] - bb32[0] + 1
val h32 = bb32[3] - bb32[1] + 1
# 2x size: ink box within [1.5x, 2.5x] of the small box (rounding slack)
assert_true(w32 * 2 >= w16 * 3)
assert_true(w32 * 2 <= w16 * 5)
assert_true(h32 * 2 >= h16 * 3)
assert_true(h32 * 2 <= h16 * 5)
```

</details>

#### rasterizes a second glyph ('O') with interior hole ink pattern

- rasterizes a second glyph ('O') with interior hole ink pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rasterizes a second glyph ('O') with interior hole ink pattern")
val cmds = vf_glyph_commands(79)
assert_true(cmds.len() > 0)
val g = rasterize_vector(cmds, 79, 24)
val bb = ink_bbox(g.pixels, g.width, g.height)
assert_true(bb[4] > 0)
# 'O' has a counter: fewer ink pixels than its full ink box area
val box_area = (bb[2] - bb[0] + 1) * (bb[3] - bb[1] + 1)
assert_true(bb[4] < box_area)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering vector font outline rasterization.
- vector font outline rasterization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `e5278440e8a62b0877de70c4c112ded248fb220a4c1e3cb91f8351907c0f4206`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e5278440e8a62b0877de70c4c112ded248fb220a4c1e3cb91f8351907c0f4206`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e5278440e8a62b0877de70c4c112ded248fb220a4c1e3cb91f8351907c0f4206`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.spl
mirror: doc/06_spec/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides a non-empty command stream and positive width for 'A'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rasterizes 'A' at size 16 with nonzero ink inside the cell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_sync_mut/text_layout/font_vector_outline_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'grows ink and metrics monotonically from size 16 to 32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
