# Texture Registry Specification

> Tests covering TextureRegistry, register/lookup, tilemap_sample_tile, TileMap real texture rendering (end-to-end via Engine2D), TileMap render-to-texture minimap (real RTT consumer).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Texture Registry Specification

## Scenarios

### TextureRegistry

### register/lookup

#### returns nil for an unregistered id

- returns nil for an unregistered id


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns nil for an unregistered id")
val reg = TextureRegistry.create()
val found = reg.lookup(1)
var is_present = false
if val Some(_t) = found:
    is_present = true
assert_false(is_present)
```

</details>

#### returns the registered texture by id

- returns the registered texture by id
   - Expected: tex.width equals `4`
   - Expected: tex.height equals `4`
   - Expected: tex.texture_id equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns the registered texture by id")
var reg = TextureRegistry.create()
reg.register(7, 4, 4, [0xFFFF0000; 16])
val found = reg.lookup(7)
var is_present = false
if val Some(_t) = found:
    is_present = true
assert_true(is_present)
if val Some(tex) = found:
    expect(tex.width).to_equal(4)
    expect(tex.height).to_equal(4)
    expect(tex.texture_id).to_equal(7)
```

</details>

#### distinguishes multiple registered ids

- distinguishes multiple registered ids
   - Expected: reg.count() equals `2`
   - Expected: t1.pixels[0] equals `0xFFAA0000`
   - Expected: t2.pixels[0] equals `0xFF00BB00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes multiple registered ids")
var reg = TextureRegistry.create()
reg.register(1, 2, 2, [0xFFAA0000; 4])
reg.register(2, 2, 2, [0xFF00BB00; 4])
expect(reg.count()).to_equal(2)
if val Some(t1) = reg.lookup(1):
    expect(t1.pixels[0]).to_equal(0xFFAA0000)
if val Some(t2) = reg.lookup(2):
    expect(t2.pixels[0]).to_equal(0xFF00BB00)
```

</details>

### tilemap_sample_tile

#### samples the left tile's real pixels from a horizontal strip

- samples the left tile's real pixels from a horizontal strip
   - Expected: pixels.len() equals `16`
   - Expected: pixels[i] equals `0xFFAA1122`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("samples the left tile's real pixels from a horizontal strip")
val tex = _build_two_tile_strip(1, 4, 4, 0xFFAA1122, 0xFF22BB44)
val pixels = tilemap_sample_tile(tex, 0, 4, 4)
expect(pixels.len()).to_equal(16)
var i = 0
while i < pixels.len():
    expect(pixels[i]).to_equal(0xFFAA1122)
    i = i + 1
```

</details>

#### samples the right tile's real pixels from a horizontal strip

- samples the right tile's real pixels from a horizontal strip
   - Expected: pixels.len() equals `16`
   - Expected: pixels[i] equals `0xFF22BB44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("samples the right tile's real pixels from a horizontal strip")
val tex = _build_two_tile_strip(1, 4, 4, 0xFFAA1122, 0xFF22BB44)
val pixels = tilemap_sample_tile(tex, 1, 4, 4)
expect(pixels.len()).to_equal(16)
var i = 0
while i < pixels.len():
    expect(pixels[i]).to_equal(0xFF22BB44)
    i = i + 1
```

</details>

#### falls back to the solid placeholder when the tile index is out of the strip's bounds

- falls back to the solid placeholder when the tile index is out of the strip's bounds
   - Expected: pixels.len() equals `16`
   - Expected: pixels[0] equals `0xFF000005`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to the solid placeholder when the tile index is out of the strip's bounds")
val tex = _build_two_tile_strip(1, 4, 4, 0xFFAA1122, 0xFF22BB44)
# Only 2 tiles (index 0,1) fit in an 8-wide strip of 4-wide tiles.
val pixels = tilemap_sample_tile(tex, 5, 4, 4)
expect(pixels.len()).to_equal(16)
# Placeholder for idx=5 packs 5 into the blue channel: 0xFF000005.
expect(pixels[0]).to_equal(0xFF000005)
```

</details>

### TileMap real texture rendering (end-to-end via Engine2D)

#### create_textured renders the registered strip's real colors, not the placeholder

- create_textured renders the registered strip's real colors, not the placeholder


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create_textured renders the registered strip's real colors, not the placeholder")
var reg = TextureRegistry.create()
val strip = _build_two_tile_strip(9, 4, 4, 0xFFAA1122, 0xFF22BB44)
reg.register(9, strip.width, strip.height, strip.pixels)
val cells = [[0, 1]]
val tm = TileMap.create_textured(9, 4, 4, cells, reg)

var engine = Engine2D.create_with_backend(32, 32, "cpu")
engine.clear(0xFF001122)
val camera = Camera2D.create(0.0, 0.0, 32.0, 32.0)
tm.render_tilemap(engine, camera, 0.0, 0.0)
engine.present()

val pixels = engine.read_pixels()
assert_true(_contains_color(pixels, 0xFFAA1122))
assert_true(_contains_color(pixels, 0xFF22BB44))
# The old placeholder colors for tile indices 0 and 1 must NOT appear —
# proves this path samples real pixels, it didn't just get lucky.
assert_false(_contains_color(pixels, 0xFF000000))
assert_false(_contains_color(pixels, 0xFF000001))
```

</details>

#### create (no registry) still falls back to the placeholder unchanged

- create (no registry) still falls back to the placeholder unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create (no registry) still falls back to the placeholder unchanged")
val cells = [[0, 1]]
val tm = TileMap.create(9, 4, 4, cells)

var engine = Engine2D.create_with_backend(32, 32, "cpu")
engine.clear(0xFF001122)
val camera = Camera2D.create(0.0, 0.0, 32.0, 32.0)
tm.render_tilemap(engine, camera, 0.0, 0.0)
engine.present()

val pixels = engine.read_pixels()
# Placeholder colors: idx 0 -> 0xFF000000, idx 1 -> 0xFF000001.
assert_true(_contains_color(pixels, 0xFF000000))
assert_true(_contains_color(pixels, 0xFF000001))
```

</details>

### TileMap render-to-texture minimap (real RTT consumer)

#### composites a 1px-per-tile minimap of real tile colors onto the parent engine

- composites a 1px-per-tile minimap of real tile colors onto the parent engine
   - Expected: pixels[0] equals `0xFFAA1122`
   - Expected: pixels[1] equals `0xFF22BB44`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("composites a 1px-per-tile minimap of real tile colors onto the parent engine")
var reg = TextureRegistry.create()
val strip = _build_two_tile_strip(11, 4, 4, 0xFFAA1122, 0xFF22BB44)
reg.register(11, strip.width, strip.height, strip.pixels)
val cells = [[0, 1]]
val tm = TileMap.create_textured(11, 4, 4, cells, reg)

var engine = Engine2D.create_with_backend(8, 8, "cpu")
engine.clear(0xFF001122)
tm.render_minimap(engine, 0, 0)
engine.present()

val pixels = engine.read_pixels()
# 8-wide canvas: (0,0) -> index 0, (1,0) -> index 1.
expect(pixels[0]).to_equal(0xFFAA1122)
expect(pixels[1]).to_equal(0xFF22BB44)
```

</details>

#### falls back to placeholder colors in the minimap when no registry is set

- falls back to placeholder colors in the minimap when no registry is set
   - Expected: pixels[0] equals `0xFF000000`
   - Expected: pixels[1] equals `0xFF000001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("falls back to placeholder colors in the minimap when no registry is set")
val cells = [[0, 1]]
val tm = TileMap.create(11, 4, 4, cells)

var engine = Engine2D.create_with_backend(8, 8, "cpu")
engine.clear(0xFF001122)
tm.render_minimap(engine, 0, 0)
engine.present()

val pixels = engine.read_pixels()
expect(pixels[0]).to_equal(0xFF000000)
expect(pixels[1]).to_equal(0xFF000001)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TextureRegistry, register/lookup, tilemap_sample_tile, TileMap real texture rendering (end-to-end via Engine2D), TileMap render-to-texture minimap (real RTT consumer).
- TextureRegistry
- register/lookup
- tilemap_sample_tile
- TileMap real texture rendering (end-to-end via Engine2D)
- TileMap render-to-texture minimap (real RTT consumer)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `74740a853e0067f8a0720a0285804cc3d3f91dcd0d24fdcf9d986742cfcf4177`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74740a853e0067f8a0720a0285804cc3d3f91dcd0d24fdcf9d986742cfcf4177`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74740a853e0067f8a0720a0285804cc3d3f91dcd0d24fdcf9d986742cfcf4177`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nil for an unregistered id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the registered texture by id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes multiple registered ids' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
