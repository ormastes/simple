# backend_software_damage_spec

> Software Backend Damage Tracking Specification (WS-D3)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# backend_software_damage_spec

Software Backend Damage Tracking Specification (WS-D3)

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Software Backend Damage Tracking Specification (WS-D3)

@tag: gpu, engine2d, software, damage, present
@cover src/lib/gc_async_mut/gpu/engine2d/backend_software.spl 40%

Damage-driven present is only safe if the dirty-tile set covers every pixel
the renderer actually wrote. A test scoped to the damaged region passes
trivially when the damage set is WRONG -- which is exactly how a stale-pixel
bug hides. Every correctness example here therefore compares the ENTIRE
framebuffer produced through the damage path against a full-redraw reference.

Regression coverage:
  * WS-D3 hole #1 -- scale_alpha_in_place() rewrote every pixel and marked
    nothing dirty.
  * WS-D3 hole #2 -- init() filled the whole buffer with opaque black while
    allocating dirty_tiles all-false, so frame 1 had empty damage.

## Scenarios

### SoftwareBackend damage tracking

### WS-D3 hole #2: init() damage covers the buffer it wrote

#### reports non-empty damage immediately after init

- reports non-empty damage immediately after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports non-empty damage immediately after init")
var b = SoftwareBackend.create()
if b.init(W, H):
    # init() fills the whole buffer with opaque black. Damage must
    # not be empty, or frame 1 ships stale pixels.
    assert_false(b.damage_is_empty())
    b.shutdown()
```

</details>

#### init damage spans the full surface

- init damage spans the full surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init damage spans the full surface")
var b = SoftwareBackend.create()
if b.init(W, H):
    val rects = b.damage_rects(16)
    assert_true(rects.len() >= 4)
    # Whole surface written => whole surface reported (the >60%
    # bound collapses this to one full-screen rect).
    assert_equal(rects.len(), 4)
    assert_equal(rects[0], 0)
    assert_equal(rects[1], 0)
    assert_equal(rects[2], W)
    assert_equal(rects[3], H)
    b.shutdown()
```

</details>

### WS-D3 hole #1: scale_alpha_in_place marks damage

#### reports non-empty damage after an in-place alpha scale

- reports non-empty damage after an in-place alpha scale


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports non-empty damage after an in-place alpha scale")
var b = SoftwareBackend.create()
if b.init(W, H):
    paint_scene(b)
    b.present()               # damage cleared
    assert_true(b.damage_is_empty())
    b.scale_alpha_in_place(500)
    assert_false(b.damage_is_empty())
    b.shutdown()
```

</details>

#### damage-driven mirror matches a full redraw after alpha scale

- damage-driven mirror matches a full redraw after alpha scale


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("damage-driven mirror matches a full redraw after alpha scale")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    # Seed the mirror, then clear damage so the next read is
    # genuinely damage-driven.
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    ref_b.scale_alpha_in_place(500)
    dmg_b.scale_alpha_in_place(500)

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

### whole-framebuffer damage correctness

#### a rect straddling a tile boundary updates every pixel

- a rect straddling a tile boundary updates every pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a rect straddling a tile boundary updates every pixel")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    # x=58..78 crosses the 64px tile seam; y=60..76 crosses y=64.
    ref_b.draw_rect_filled(58, 60, 20, 16, 0xFF00FF00)
    dmg_b.draw_rect_filled(58, 60, 20, 16, 0xFF00FF00)

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

#### a 1px horizontal line on a tile seam updates every pixel

- a 1px horizontal line on a tile seam updates every pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a 1px horizontal line on a tile seam updates every pixel")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    ref_b.draw_rect_filled(0, 64, W, 1, 0xFFFF00FF)
    dmg_b.draw_rect_filled(0, 64, W, 1, 0xFFFF00FF)

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

#### an alpha-blended draw updates every pixel

- an alpha-blended draw updates every pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an alpha-blended draw updates every pixel")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    ref_b.draw_rect_filled(20, 20, 70, 70, 0x8000FFFF)
    dmg_b.draw_rect_filled(20, 20, 70, 70, 0x8000FFFF)

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

#### a draw_image straddling a tile boundary updates every pixel

- a draw_image straddling a tile boundary updates every pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a draw_image straddling a tile boundary updates every pixel")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    # 24x24 image landing at (54,54): crosses both the x=64 and
    # y=64 tile seams. Opaque arm of draw_image.
    var img: [u32] = [0; 576]
    var p = 0
    while p < 576:
        img[p] = 0xFF00C0FF
        p = p + 1
    ref_b.draw_image(54, 54, 24, 24, img)
    dmg_b.draw_image(54, 54, 24, 24, img)

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

#### a draw_image_blend straddling a tile boundary updates every pixel

- a draw_image_blend straddling a tile boundary updates every pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a draw_image_blend straddling a tile boundary updates every pixel")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    var img: [u32] = [0; 576]
    var p = 0
    while p < 576:
        img[p] = 0x90FF3060
        p = p + 1
    ref_b.draw_image_blend(54, 54, 24, 24, img)
    dmg_b.draw_image_blend(54, 54, 24, 24, img)

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

#### a clipped draw updates every pixel

- a clipped draw updates every pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a clipped draw updates every pixel")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    # The clip rect is deliberately offset from the tile grid so a
    # mark computed on the PRE-clip rect would over/under-cover.
    ref_b.set_clip(70, 70, 30, 30)
    dmg_b.set_clip(70, 70, 30, 30)
    ref_b.draw_rect_filled(20, 20, 120, 120, 0xFF20E020)
    dmg_b.draw_rect_filled(20, 20, 120, 120, 0xFF20E020)
    ref_b.clear_clip()
    dmg_b.clear_clip()

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

#### a masked slow-path draw updates every pixel

- a masked slow-path draw updates every pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a masked slow-path draw updates every pixel")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    # Sparse mask: forces the per-pixel masked slow path.
    var mask: [u8] = [0; W * H]
    var m = 0
    while m < W * H:
        if (m % 3) == 0:
            mask[m] = 255
        m = m + 1
    ref_b.set_mask(mask, W, H)
    dmg_b.set_mask(mask, W, H)
    ref_b.draw_rect_filled(50, 50, 60, 60, 0xFFE0E020)
    dmg_b.draw_rect_filled(50, 50, 60, 60, 0xFFE0E020)
    ref_b.clear_mask()
    dmg_b.clear_mask()

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

#### a clear() repaints every pixel through the damage path

- a clear() repaints every pixel through the damage path


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a clear() repaints every pixel through the damage path")
var ref_b = SoftwareBackend.create()
var dmg_b = SoftwareBackend.create()
if ref_b.init(W, H) and dmg_b.init(W, H):
    paint_scene(ref_b)
    paint_scene(dmg_b)
    val seeded = dmg_b.read_pixels_damaged(16)
    assert_equal(seeded.len(), W * H)
    dmg_b.present()

    ref_b.clear(0xFF224466)
    dmg_b.clear(0xFF224466)

    val truth = ref_b.read_pixels()
    val mirror = dmg_b.read_pixels_damaged(16)
    assert_equal(count_mismatches(mirror, truth), 0)
    ref_b.shutdown()
    dmg_b.shutdown()
```

</details>

### damage set shape

#### vertically merges every separated run from the prior row

- vertically merges every separated run from the prior row


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vertically merges every separated run from the prior row")
var b = SoftwareBackend.create()
b.w = 256
b.h = 128
b.tiles_x = 4
b.tiles_y = 2
b.dirty_tiles = [
    true, false, true, false,
    true, false, true, false,
]
val rects = b.damage_rects(16)
assert_equal(rects, [0, 0, 64, 128, 128, 0, 64, 128])
```

</details>

#### uses widened area arithmetic for an 8K fallback decision

- uses widened area arithmetic for an 8K fallback decision


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses widened area arithmetic for an 8K fallback decision")
var b = SoftwareBackend.create()
b.w = 7680
b.h = 4320
b.tiles_x = 120
b.tiles_y = 68
b.dirty_tiles = [false; 8160]
# The first 100 of 120 columns cover 83.3% of the viewport.  The
# bottom row is ragged (32px), so this also exercises clipping.
var ty = 0
while ty < 68:
    var tx = 0
    while tx < 100:
        b.dirty_tiles[ty * 120 + tx] = true
        tx += 1
    ty += 1
val rects = b.damage_rects(16)
assert_equal(rects, [0, 0, 7680, 4320])
```

</details>

#### packs only dirty tile rows in deterministic plan order without clearing damage

- packs only dirty tile rows in deterministic plan order without clearing damage


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("packs only dirty tile rows in deterministic plan order without clearing damage")
var b = SoftwareBackend.create()
if b.init(W, H):
    b.clear(0xFF101820u32)
    b.present()
    # One write at (70,70) dirties exactly tile [64,64,128,128).
    b.draw_rect_filled(70, 70, 2, 2, 0xFF00FF00u32)
    val packed = b.read_damage_pixels_packed(16)
    assert_true(packed.valid)
    assert_equal(packed.rects, [64, 64, 64, 64])
    assert_equal(packed.pixels.len(), 64 * 64)
    val full = b.read_pixels()
    # Packed order is rectangle-major then row-major, so the
    # first pixel and the locally changed pixel have exact source
    # coordinates in the current framebuffer.
    assert_equal(packed.pixels[0], full[64 + 64 * W])
    assert_equal(packed.pixels[6 + 6 * 64], 0xFF00FF00u32)
    # Extraction is not presentation: retry remains possible.
    assert_false(b.damage_is_empty())
    b.shutdown()
```

</details>

#### concatenates disjoint dirty rectangles without widening their payload

- concatenates disjoint dirty rectangles without widening their payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("concatenates disjoint dirty rectangles without widening their payload")
var b = SoftwareBackend.create()
if b.init(512, 128):
    b.clear(0xFF101820u32)
    b.present()
    b.draw_rect_filled(2, 2, 1, 1, 0xFF112233u32)
    b.draw_rect_filled(258, 2, 1, 1, 0xFF445566u32)
    val packed = b.read_damage_pixels_packed(16)
    assert_true(packed.valid)
    assert_equal(packed.rects, [0, 0, 64, 64, 256, 0, 64, 64])
    assert_equal(packed.pixels.len(), 2 * 64 * 64)
    assert_equal(packed.pixels[2 + 2 * 64], 0xFF112233u32)
    assert_equal(packed.pixels[64 * 64 + 2 + 2 * 64], 0xFF445566u32)
    b.shutdown()
```

</details>

#### a no-op frame yields zero rects

- a no-op frame yields zero rects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a no-op frame yields zero rects")
var b = SoftwareBackend.create()
if b.init(W, H):
    paint_scene(b)
    b.present()
    assert_equal(b.damage_rects(16).len(), 0)
    assert_true(b.damage_is_empty())
    b.shutdown()
```

</details>

#### a small draw yields a small, bounded damage set

- a small draw yields a small, bounded damage set


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a small draw yields a small, bounded damage set")
var b = SoftwareBackend.create()
if b.init(W, H):
    paint_scene(b)
    b.present()
    b.draw_rect_filled(4, 4, 8, 8, 0xFFFFFFFF)
    val rects = b.damage_rects(16)
    # One 64x64 tile touched => exactly one rect, and it must be
    # far smaller than the surface.
    assert_equal(rects.len(), 4)
    assert_true(rects[2] * rects[3] < W * H)
    b.shutdown()
```

</details>

#### the rect count never exceeds the cap

- the rect count never exceeds the cap


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("the rect count never exceeds the cap")
# A wide surface so the damage BOUND stays well under 60% of the
# area -- otherwise the 60% full-surface rule fires first and the
# cap branch is never evaluated (that made an earlier version of
# this example vacuous).
var b = SoftwareBackend.create()
if b.init(640, 512):
    b.clear(0xFF101820)
    b.present()
    # Five isolated dirty tiles along a single tile row: bound is
    # 576x64 of 640x512 == 11% of the surface.
    var x = 2
    while x < 576:
        b.draw_rect_filled(x, 2, 1, 1, 0xFFFFFFFF)
        x = x + 128
    val uncapped = b.damage_rects(16)
    assert_equal(uncapped.len() / 4, 5)
    val capped = b.damage_rects(3)
    assert_equal(capped.len() / 4, 1)
    assert_true(capped[2] < 640)
    b.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `1a2773787887353331ad32d7f2bb652ecfd655632343227913e9cb09c3c568d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a2773787887353331ad32d7f2bb652ecfd655632343227913e9cb09c3c568d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a2773787887353331ad32d7f2bb652ecfd655632343227913e9cb09c3c568d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_damage_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_damage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/backend_software_damage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports non-empty damage immediately after init' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'init damage spans the full surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/backend_software_damage_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports non-empty damage after an in-place alpha scale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
