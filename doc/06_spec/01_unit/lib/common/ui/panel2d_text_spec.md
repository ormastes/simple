# Panel2D text — font hub wiring spec

> Covers the text-carrying additions to `src/lib/common/ui/panel2d.spl`: `panel_with_text`/`panel_with_text_family` attach text to a panel, `panel_text_extents` measures it through the ONE FontRenderer hub (never a rasterizer directly — no fourth rasterizer per D7), and `panel_to_draw_ir_batch` emits a measured `draw_text` DrawIrCommand whose `hit_rect` is the MEASURED extent, not the panel's declared/guessed rect.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Panel2D text — font hub wiring spec

Covers the text-carrying additions to `src/lib/common/ui/panel2d.spl`: `panel_with_text`/`panel_with_text_family` attach text to a panel, `panel_text_extents` measures it through the ONE FontRenderer hub (never a rasterizer directly — no fourth rasterizer per D7), and `panel_to_draw_ir_batch` emits a measured `draw_text` DrawIrCommand whose `hit_rect` is the MEASURED extent, not the panel's declared/guessed rect.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | N/A (Lane L5 of the unified 2D event/panel/offload campaign) |
| Category | Stdlib / UI |
| Status | Implemented |
| Plan | doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md |
| Source | `test/01_unit/lib/common/ui/panel2d_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Covers the text-carrying additions to `src/lib/common/ui/panel2d.spl`:
`panel_with_text`/`panel_with_text_family` attach text to a panel,
`panel_text_extents` measures it through the ONE FontRenderer hub (never a
rasterizer directly — no fourth rasterizer per D7), and
`panel_to_draw_ir_batch` emits a measured `draw_text` DrawIrCommand whose
`hit_rect` is the MEASURED extent, not the panel's declared/guessed rect.

Two font tiers are exercised: bitmap (deterministic built-in 8x16 VGA
glyphs, no file I/O — `FontRenderer.bitmap_only()`) and vector (the
production `resolve_font_metrics_with_language` hub path — the same one
`widget_draw_ir`'s `_default_text` already uses). The vector-tier scenario
does not fabricate a measurement: it asserts on whatever the hub honestly
reports, valid or not, so a missing font file on disk is a real, visible
`valid: false` rather than a shipped fake number.

## Scenarios

### panel_text_extents — bitmap tier (deterministic, no file I/O)

#### measures ASCII text deterministically at the 8x16 base size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- measures ASCII text deterministically at the 8x16 base size
- measure the same ASCII text twice at font_size 16
   - Expected: a.advances.len() equals `2`
   - Expected: b.advances.len() equals `2`
   - Expected: a.width equals `b.width`
   - Expected: a.line_height equals `b.line_height`
   - Expected: a.advances[0] equals `b.advances[0]`
   - Expected: a.advances[1] equals `b.advances[1]`
   - Expected: a.advances[0] equals `8`
   - Expected: a.advances[1] equals `8`
   - Expected: a.width equals `16`
   - Expected: a.line_height equals `16`
   - Expected: a.identity equals `bitmap-8x16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("measures ASCII text deterministically at the 8x16 base size")
step("measure the same ASCII text twice at font_size 16")
val a = panel_text_extents("Hi", PANEL_FONT_TIER_BITMAP, 16, "")
val b = panel_text_extents("Hi", PANEL_FONT_TIER_BITMAP, 16, "")
assert_true(a.valid)
assert_true(b.valid)
expect(a.advances.len()).to_equal(2)
expect(b.advances.len()).to_equal(2)
# Same input, same tier, same size -> identical measurement both times.
expect(a.width).to_equal(b.width)
expect(a.line_height).to_equal(b.line_height)
expect(a.advances[0]).to_equal(b.advances[0])
expect(a.advances[1]).to_equal(b.advances[1])
# Monospace built-in VGA glyph: 8px advance per char at font_size<=16.
expect(a.advances[0]).to_equal(8)
expect(a.advances[1]).to_equal(8)
expect(a.width).to_equal(16)
expect(a.line_height).to_equal(16)
expect(a.identity).to_equal("bitmap-8x16")
```

</details>

#### scales the bitmap advance and line height above the 16px base

- scales the bitmap advance and line height above the 16px base
- measure a single char at font_size 32 (2x scale)
   - Expected: extents.advances.len() equals `1`
   - Expected: extents.advances[0] equals `16`
   - Expected: extents.width equals `16`
   - Expected: extents.line_height equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("scales the bitmap advance and line height above the 16px base")
step("measure a single char at font_size 32 (2x scale)")
val extents = panel_text_extents("A", PANEL_FONT_TIER_BITMAP, 32, "")
assert_true(extents.valid)
expect(extents.advances.len()).to_equal(1)
expect(extents.advances[0]).to_equal(16)
expect(extents.width).to_equal(16)
expect(extents.line_height).to_equal(32)
```

</details>

#### reports an empty measurement (not a guess) for empty text

- reports an empty measurement (not a guess) for empty text
- measure empty text
   - Expected: extents.width equals `0`
   - Expected: extents.line_height equals `0`
   - Expected: extents.advances.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an empty measurement (not a guess) for empty text")
step("measure empty text")
val extents = panel_text_extents("", PANEL_FONT_TIER_BITMAP, 16, "")
assert_false(extents.valid)
expect(extents.width).to_equal(0)
expect(extents.line_height).to_equal(0)
expect(extents.advances.len()).to_equal(0)
```

</details>

### panel_text_extents — vector tier (routes through the FontRenderer hub)

#### routes to resolve_font_metrics_with_language and never fabricates a measurement

- routes to resolve_font_metrics_with_language and never fabricates a measurement
- measure through the vector tier with no font pinned/registered by this spec
   - Expected: extents.advances.len() equals `2`
   - Expected: extents.width equals `0`
   - Expected: extents.line_height equals `0`
   - Expected: extents.advances.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes to resolve_font_metrics_with_language and never fabricates a measurement")
step("measure through the vector tier with no font pinned/registered by this spec")
val extents = panel_text_extents("Hi", PANEL_FONT_TIER_VECTOR, 16, "sans")
# The hub is consulted for real; this spec makes no assumption about
# whether a system font happens to be resolvable in the environment
# it runs in. Either way the result must be internally honest:
# invalid means a zeroed-out, unmeasured report (matching
# draw_ir_text_resolved_font's own guard), valid means a real,
# hub-sourced measurement -- never a value this spec invented.
if extents.valid:
    expect(extents.advances.len()).to_equal(2)
    assert_true(extents.width >= 0)
    assert_true(extents.line_height >= 0)
    # A real hub resolution carries the resolved font's own
    # identity, never this module's bitmap-tier sentinel string.
    assert_false(extents.identity == "bitmap-8x16")
else:
    expect(extents.width).to_equal(0)
    expect(extents.line_height).to_equal(0)
    expect(extents.advances.len()).to_equal(0)
```

</details>

### panel_to_draw_ir_batch — text command emission

#### a bitmap-tier text panel's batch carries a measured draw_text command

- a bitmap-tier text panel's batch carries a measured draw_text command
- root panel carrying bitmap-tier text 'Hi' at font_size 16
   - Expected: batch.commands.len() equals `1`
   - Expected: cmd.kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: cmd.text_value equals `Hi`
   - Expected: cmd.advance_widths.len() equals `2`
   - Expected: cmd.hit_rect.width equals `16`
   - Expected: cmd.hit_rect.height equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a bitmap-tier text panel's batch carries a measured draw_text command")
step("root panel carrying bitmap-tier text 'Hi' at font_size 16")
val root = panel_with_text(panel2d("label", 10, 20, 200, 50), "Hi", PANEL_FONT_TIER_BITMAP, 16)
val batch = panel_to_draw_ir_batch(root)
expect(batch.commands.len()).to_equal(1)
val cmd = batch.commands[0]
expect(cmd.kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(cmd.text_value).to_equal("Hi")
expect(cmd.advance_widths.len()).to_equal(2)
assert_true(cmd.hit_rect.present)
expect(cmd.hit_rect.width).to_equal(16)
expect(cmd.hit_rect.height).to_equal(16)
```

</details>

#### a text child panel is hit-testable at its measured extents, not its declared (guessed) rect

- a text child panel is hit-testable at its measured extents, not its declared (guessed) rect
- child declares a large 200x80 rect but carries short bitmap-tier text
   - Expected: batch.commands.len() equals `1`
   - Expected: cmd.kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: cmd.hit_rect.width equals `16`
   - Expected: cmd.hit_rect.height equals `16`
   - Expected: cmd.hit_rect.x equals `5`
   - Expected: cmd.hit_rect.y equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a text child panel is hit-testable at its measured extents, not its declared (guessed) rect")
step("child declares a large 200x80 rect but carries short bitmap-tier text")
var root = panel2d("root", 0, 0, 300, 300)
val child = panel_with_text(panel2d("label", 5, 5, 200, 80), "Hi", PANEL_FONT_TIER_BITMAP, 16)
root = panel_add_child(root, child)
val batch = panel_to_draw_ir_batch(root)
expect(batch.commands.len()).to_equal(1)
val cmd = batch.commands[0]
expect(cmd.kind).to_equal(DRAW_IR_COMMAND_TEXT)
# Measured 16x16, NOT the declared 200x80 -- the hit rect follows
# panel_text_extents, never the panel's own rect for text panels.
expect(cmd.hit_rect.width).to_equal(16)
expect(cmd.hit_rect.height).to_equal(16)
expect(cmd.hit_rect.x).to_equal(5)
expect(cmd.hit_rect.y).to_equal(5)
```

</details>

#### panel_with_text_family carries an explicit vector-tier family through to the batch

- panel_with_text_family carries an explicit vector-tier family through to the batch
- root carrying vector-tier text with an explicit family
   - Expected: batch.commands.len() equals `1`
   - Expected: cmd.kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: cmd.text_value equals `Hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("panel_with_text_family carries an explicit vector-tier family through to the batch")
step("root carrying vector-tier text with an explicit family")
val root = panel_with_text_family(panel2d("label", 0, 0, 200, 50), "Hi", PANEL_FONT_TIER_VECTOR, 16, "serif")
val batch = panel_to_draw_ir_batch(root)
expect(batch.commands.len()).to_equal(1)
val cmd = batch.commands[0]
expect(cmd.kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(cmd.text_value).to_equal("Hi")
# Whatever the hub resolves (or honestly fails to), the command
# stays hit-testable: _panel_leaf_command always sets a present
# hit_rect, falling back to the panel's own declared rect (200x50)
# only when the hub reports an invalid/unmeasured extent -- never
# leaving the panel unhittable and never fabricating a font metric.
assert_true(cmd.hit_rect.present)
assert_true(cmd.hit_rect.width == 200 or cmd.hit_rect.width > 0)
assert_true(cmd.hit_rect.height == 50 or cmd.hit_rect.height > 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/unified_2d_engine/unified_2d_event_panel_offload_2026-07-30.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a89818464ad2a59a3f9f88929f226a1e5aed1246ab2b9c89205b14c7bf251df`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a89818464ad2a59a3f9f88929f226a1e5aed1246ab2b9c89205b14c7bf251df`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a89818464ad2a59a3f9f88929f226a1e5aed1246ab2b9c89205b14c7bf251df`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/panel2d_text_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/panel2d_text_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/panel2d_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/panel2d_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/panel2d_text_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 27 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/panel2d_text_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'measures ASCII text deterministically at the 8x16 base size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/panel2d_text_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scales the bitmap advance and line height above the 16px base' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/panel2d_text_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports an empty measurement (not a guess) for empty text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
