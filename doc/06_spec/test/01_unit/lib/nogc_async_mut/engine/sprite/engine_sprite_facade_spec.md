# Engine Sprite Facade Specification

> 1. var atlas = TextureAtlas create

<!-- sdn-diagram:id=engine_sprite_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_sprite_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_sprite_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_sprite_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Sprite Facade Specification

## Scenarios

### nogc_async_mut engine sprite facade

#### re-exports texture, atlas, sprite, and builder behavior

1. var atlas = TextureAtlas create
   - Expected: region.width equals `2`
   - Expected: region.height equals `2`
   - Expected: sheet.frame_count() equals `4`
   - Expected: animator.current_frame() equals `0`
2. var builder = AtlasBuilder new
3. builder add sprite
   - Expected: layout.sprite_count() equals `1`
   - Expected: packed_sprite.name equals `hero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val packed = pack_color(color)
expect(packed).to_be_greater_than(0)
expect(unpack_color(packed).r).to_be_greater_than(0.99)
val tex = Texture.create_solid(2, 2, color)
expect(tex.width).to_equal(2)
expect(tex.pixels.len()).to_equal(4)
var atlas = TextureAtlas.create(8, 8)
val region = atlas.pack(2, 2, tex.pixels)
expect(region.width).to_equal(2)
expect(region.height).to_equal(2)
val tid = TextureId(raw: RawHandle.new(0, 1))
val sheet = SpriteSheet.create(tid, 16, 16, 2, 2)
expect(sheet.frame_count()).to_equal(4)
val animator = SpriteAnimator.create(sheet)
expect(animator.current_frame()).to_equal(0)
var builder = AtlasBuilder.new(1)
builder.add_sprite("hero", 16, 16)
val layout = builder.pack()
expect(layout.sprite_count()).to_equal(1)
val packed_sprite = layout.sprites[0]
expect(packed_sprite.name).to_equal("hero")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/engine/sprite/engine_sprite_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut engine sprite facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
