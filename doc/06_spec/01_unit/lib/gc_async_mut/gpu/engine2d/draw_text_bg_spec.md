# Draw Text Bg Specification

> Tests covering Engine2DExtended.draw_text_bg (CPU backend).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Text Bg Specification

## Scenarios

### Engine2DExtended.draw_text_bg (CPU backend)

#### extracts and colorizes only a bounded glyph atlas subrect

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts and colorizes only a bounded glyph atlas subrect
   - Expected: pixels equals `[0x40402010u32, 0x80402010u32]`
   - Expected: engine2d_font_atlas_subrect_pixels(atlas, 3, 2, 2, 1, 2, 1, 0xFFFFFFFFu32).len() equals `0`
   - Expected: engine2d_font_atlas_subrect_pixels([], 2147483647, 2, 0, 0, 1, 1, 0xFFFFFFFFu32).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts and colorizes only a bounded glyph atlas subrect")
val atlas = [
    0u32, 0u32, 0u32,
    0u32, 0x80FFFFFFu32, 0xFFFFFFFFu32
]
val pixels = engine2d_font_atlas_subrect_pixels(atlas, 3, 2, 1, 1, 2, 1, 0x80402010u32)

expect(pixels).to_equal([0x40402010u32, 0x80402010u32])
expect(engine2d_font_atlas_subrect_pixels(atlas, 3, 2, 2, 1, 2, 1, 0xFFFFFFFFu32).len()).to_equal(0)
expect(engine2d_font_atlas_subrect_pixels([], 2147483647, 2, 0, 0, 1, 1, 0xFFFFFFFFu32).len()).to_equal(0)
```

</details>

#### glyph cell vs outside

#### paints bg inside the glyph cell and preserves clear outside

- paints bg inside the glyph cell and preserves clear outside
   - Expected: pixels[outside_idx] equals `GREEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("paints bg inside the glyph cell and preserves clear outside")
val GREEN: u32 = 0xFF00FF00
val BLACK: u32 = 0xFF000000
val WHITE: u32 = 0xFFFFFFFF

var engine = Engine2D.create_with_backend(32, 16, "cpu")
engine.clear(GREEN)

# Paint a single 'A' glyph at the origin with 16pt font. The
# draw_text_bg contract says the glyph cell fills with BLACK
# and glyph foreground pixels are WHITE. Pixels outside the
# cell must stay GREEN.
engine.draw_text_bg(0, 0, "A", WHITE, BLACK, 16)
engine.present()

val pixels = engine.read_pixels()

# Cell-outside pixel (far right of the 32-wide scene) must
# remain GREEN — draw_text_bg must not scribble on the whole
# framebuffer.
val outside_idx = 8 * 32 + 30
expect(pixels[outside_idx]).to_equal(GREEN)

# Cell-inside pixel (column 0 bottom row of the glyph cell)
# must have been overwritten by the background/text path, but
# may be BLACK, WHITE, or antialiased text coverage depending
# on the active shared font renderer.
val inside_idx = 15 * 32 + 0
val inside = pixels[inside_idx]
expect(inside != GREEN).to_be(true)

engine.shutdown()
```

</details>

#### blends glyph edge coverage between bg and fg (per-pixel AA)

- blends glyph edge coverage between bg and fg (per-pixel AA)


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blends glyph edge coverage between bg and fg (per-pixel AA)")
# Per-pixel AA-preserving contract: output pixels that straddle
# an on/off boundary of the 5x7 binary font must take on a
# value strictly between pure bg and pure fg, not snap to one
# or the other. This proves draw_text_bg is blending glyph
# coverage instead of doing a bg-rect + opaque-glyph overlay.
val BLACK: u32 = 0xFF000000
val WHITE: u32 = 0xFFFFFFFF

var engine = Engine2D.create_with_backend(32, 16, "cpu")
engine.clear(BLACK)
# font_size=16 -> scale = 16/7 = 2, glyph cell = 10x14.
# For 'A' row 0 = 0b01110, the top-edge sub-pixel at output
# coord (3, 0) bilinearly samples neighbors spanning the
# off-above / on-below boundary, so coverage is ~0.75 and
# the red channel lands near 191 — clearly not 0 or 255.
engine.draw_text_bg(0, 0, "A", WHITE, BLACK, 16)
engine.present()

val pixels = engine.read_pixels()
expect(_has_intermediate_red(pixels, 32, 0, 0, 16, 16)).to_be(true)

engine.shutdown()
```

</details>

#### returns without panic on an empty string

- returns without panic on an empty string
   - Expected: pixels[0] equals `GREEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns without panic on an empty string")
val GREEN: u32 = 0xFF00FF00
var engine = Engine2D.create_with_backend(16, 16, "cpu")
engine.clear(GREEN)
engine.draw_text_bg(2, 2, "", 0xFFFFFFFF, 0xFF000000, 16)
engine.present()
val pixels = engine.read_pixels()
# Empty string must touch no pixels — whole scene still GREEN.
expect(pixels[0]).to_equal(GREEN)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Engine2DExtended.draw_text_bg (CPU backend).
- Engine2DExtended.draw_text_bg (CPU backend)

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7545893bd6794edf001c39f1c7ecf154d78536fe8787876614cd94de519d07f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7545893bd6794edf001c39f1c7ecf154d78536fe8787876614cd94de519d07f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7545893bd6794edf001c39f1c7ecf154d78536fe8787876614cd94de519d07f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts and colorizes only a bounded glyph atlas subrect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paints bg inside the glyph cell and preserves clear outside' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_text_bg_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blends glyph edge coverage between bg and fg (per-pixel AA)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
