# sprite_spec

> Engine Sprite/Texture System Tests

<!-- sdn-diagram:id=sprite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sprite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sprite_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sprite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sprite_spec

Engine Sprite/Texture System Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/sprite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Sprite/Texture System Tests

Tests Texture, TextureStore, SpriteSheet, TextureAtlas.

## Scenarios

### Texture

#### creates a texture with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex = Texture.create(64, 32)
expect(tex.width).to_equal(64)
expect(tex.height).to_equal(32)
```

</details>

#### starts with all-zero pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex = Texture.create(4, 4)
expect(tex.pixels.len()).to_equal(16)
expect(tex.pixels[0]).to_equal(0)
```

</details>

#### sets and gets a pixel

1. var tex = Texture create
2. tex set pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tex = Texture.create(8, 8)
val red = EngineColor.red()
tex.set_pixel(2, 3, red)
val got = tex.get_pixel(2, 3)
# Red channel should be ~1.0
val ri = got.r * 1000.0
expect(ri).to_be_greater_than(999.0)
expect(ri).to_be_less_than(1001.0)
# Green should be ~0.0
val gi = got.g * 1000.0
expect(gi).to_be_greater_than(-1.0)
expect(gi).to_be_less_than(2.0)
```

</details>

#### creates a solid color texture

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex = Texture.create_solid(4, 4, EngineColor.blue())
val px = tex.get_pixel(0, 0)
val bi = px.b * 1000.0
expect(bi).to_be_greater_than(999.0)
expect(bi).to_be_less_than(1001.0)
```

</details>

### pack/unpack color

#### round-trips through pack and unpack

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = EngineColor.rgba(1.0, 0.5, 0.0, 1.0)
val packed = pack_color(original)
val restored = unpack_color(packed)
# Red channel should round-trip precisely
val ri = restored.r * 1000.0
expect(ri).to_be_greater_than(999.0)
expect(ri).to_be_less_than(1001.0)
```

</details>

### TextureStore

#### adds and retrieves a texture

1. var store = TextureStore new
   - Expected: tid.is_valid() is true
   - Expected: t.width equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = TextureStore.new()
val tex = Texture.create(16, 16)
val tid = store.add(tex)
expect(tid.is_valid()).to_equal(true)
val got = store.get(tid)
if val Some(t) = got:
    expect(t.width).to_equal(16)
```

</details>

#### returns nil for invalid texture id

1. var store = TextureStore new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = TextureStore.new()
val bad_id = TextureId.invalid()
val result = store.get(bad_id)
expect(result).to_be_nil
```

</details>

#### removes a texture

1. var store = TextureStore new
   - Expected: removed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = TextureStore.new()
val tex = Texture.create(8, 8)
val tid = store.add(tex)
val removed = store.remove(tid)
expect(removed).to_equal(true)
val gone = store.get(tid)
expect(gone).to_be_nil
```

</details>

### SpriteSheet

#### computes frame rect for first frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val sheet = SpriteSheet.create(tex_id, 32, 32, 4, 2)
val rect = sheet.frame_rect(0)
expect(rect.x).to_equal(0.0)
expect(rect.y).to_equal(0.0)
expect(rect.width).to_equal(32.0)
expect(rect.height).to_equal(32.0)
```

</details>

#### computes frame rect for second row

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val sheet = SpriteSheet.create(tex_id, 32, 32, 4, 2)
# Frame 4 = row 1, col 0
val rect = sheet.frame_rect(4)
expect(rect.x).to_equal(0.0)
expect(rect.y).to_equal(32.0)
```

</details>

#### returns total frame count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tex_id = TextureId(raw: RawHandle.new(0, 1))
val sheet = SpriteSheet.create(tex_id, 16, 16, 8, 4)
expect(sheet.frame_count()).to_equal(32)
```

</details>

### TextureAtlas

#### creates an empty atlas

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val atlas = TextureAtlas.create(16, 16)
expect(atlas.region_count()).to_equal(0)
```

</details>

#### packs a sub-image and returns a region

1. var atlas = TextureAtlas create
2. pixels push
   - Expected: region.width equals `4`
   - Expected: region.height equals `4`
   - Expected: atlas.region_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var atlas = TextureAtlas.create(16, 16)
# Create a small 4x4 pixel array
var pixels: [i64] = []
var i = 0
while i < 16:
    pixels.push(pack_color(EngineColor.red()))
    i = i + 1
val maybe_region = atlas.pack(4, 4, pixels)
if val Some(region) = maybe_region:
    expect(region.width).to_equal(4)
    expect(region.height).to_equal(4)
expect(atlas.region_count()).to_equal(1)
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


</details>
