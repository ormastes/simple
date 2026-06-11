# Texture3d Specification

> <details>

<!-- sdn-diagram:id=texture3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=texture3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

texture3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=texture3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Texture3d Specification

## Scenarios

### Stream F: TextureCache3D

### texture_cache_new

#### AC-7: new cache has no entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = texture_cache_new()
expect(cache.ids.length).to_equal(0)
```

</details>

#### AC-7: new cache next_id starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = texture_cache_new()
expect(cache.next_id).to_equal(0)
```

</details>

### texture_cache_upload

#### AC-7: upload returns an id >= 0

1. var cache = texture cache new
2. var backend = make software backend inited


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = texture_cache_new()
var backend = make_software_backend_inited()
val pixels = make_2x2_rgba_pixels()
val id = texture_cache_upload(cache, backend, 2, 2, TextureFormat3D.Rgba8Unorm, pixels)
expect(id).to_be_greater_than(-1)
```

</details>

#### AC-7: upload increments cache entry count by 1

1. var cache = texture cache new
2. var backend = make software backend inited
   - Expected: cache.ids.length equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = texture_cache_new()
var backend = make_software_backend_inited()
val pixels = make_2x2_rgba_pixels()
val _ = texture_cache_upload(cache, backend, 2, 2, TextureFormat3D.Rgba8Unorm, pixels)
expect(cache.ids.length).to_equal(1)
```

</details>

#### AC-7: two uploads produce distinct ids

1. var cache = texture cache new
2. var backend = make software backend inited
   - Expected: distinct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = texture_cache_new()
var backend = make_software_backend_inited()
val pixels = make_2x2_rgba_pixels()
val id1 = texture_cache_upload(cache, backend, 2, 2, TextureFormat3D.Rgba8Unorm, pixels)
val id2 = texture_cache_upload(cache, backend, 2, 2, TextureFormat3D.Rgba8Unorm, pixels)
val distinct = id1 != id2
expect(distinct).to_equal(true)
```

</details>

### texture_cache_get

#### AC-7: get returns valid TextureHandle for uploaded id

1. var cache = texture cache new
2. var backend = make software backend inited


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = texture_cache_new()
var backend = make_software_backend_inited()
val pixels = make_2x2_rgba_pixels()
val id = texture_cache_upload(cache, backend, 2, 2, TextureFormat3D.Rgba8Unorm, pixels)
val handle = texture_cache_get(cache, id)
expect(handle.id).to_be_greater_than(-1)
```

</details>

#### AC-7: get for unknown id returns invalid handle

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache = texture_cache_new()
val handle = texture_cache_get(cache, 9999)
expect(handle.id).to_equal(-1)
```

</details>

### texture_cache_evict

#### AC-7: evict removes entry from cache

1. var cache = texture cache new
2. var backend = make software backend inited
3. texture cache evict
   - Expected: handle.id equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = texture_cache_new()
var backend = make_software_backend_inited()
val pixels = make_2x2_rgba_pixels()
val id = texture_cache_upload(cache, backend, 2, 2, TextureFormat3D.Rgba8Unorm, pixels)
texture_cache_evict(cache, id)
val handle = texture_cache_get(cache, id)
expect(handle.id).to_equal(-1)
```

</details>

### Stream F: TextureAtlas3D

### atlas_new

#### AC-7: atlas texture handle is valid after creation

1. var backend = make software backend inited


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val atlas = atlas_new(backend, 512, 512)
expect(atlas.atlas_texture.id).to_be_greater_than(-1)
```

</details>

#### AC-7: atlas starts with no rects

1. var backend = make software backend inited
   - Expected: atlas.rects.length equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val atlas = atlas_new(backend, 512, 512)
expect(atlas.rects.length).to_equal(0)
```

</details>

#### AC-7: atlas stores correct width and height

1. var backend = make software backend inited
   - Expected: atlas.atlas_width equals `512`
   - Expected: atlas.atlas_height equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val atlas = atlas_new(backend, 512, 512)
expect(atlas.atlas_width).to_equal(512)
expect(atlas.atlas_height).to_equal(512)
```

</details>

### atlas_pack

#### AC-7: pack returns rect with non-zero width and height

1. var backend = make software backend inited
2. var atlas = atlas new
   - Expected: rect.width equals `4`
   - Expected: rect.height equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
var atlas = atlas_new(backend, 512, 512)
val pixels = make_4x4_rgba_pixels()
val rect = atlas_pack(atlas, backend, 100, pixels, 4, 4)
expect(rect.width).to_equal(4)
expect(rect.height).to_equal(4)
```

</details>

#### AC-7: pack returns uv coords in range 0.0..1.0

1. var backend = make software backend inited
2. var atlas = atlas new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
var atlas = atlas_new(backend, 512, 512)
val pixels = make_4x4_rgba_pixels()
val rect = atlas_pack(atlas, backend, 101, pixels, 4, 4)
expect(rect.u0).to_be_greater_than(-1.0)
expect(rect.u1).to_be_less_than(2.0)
```

</details>

#### AC-7: pack stores rect in atlas rects list

1. var backend = make software backend inited
2. var atlas = atlas new
   - Expected: atlas.rects.length equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
var atlas = atlas_new(backend, 512, 512)
val pixels = make_4x4_rgba_pixels()
val _ = atlas_pack(atlas, backend, 102, pixels, 4, 4)
expect(atlas.rects.length).to_equal(1)
```

</details>

### atlas_lookup

#### AC-7: lookup returns same rect as pack

1. var backend = make software backend inited
2. var atlas = atlas new
   - Expected: found.width equals `packed.width`
   - Expected: found.height equals `packed.height`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
var atlas = atlas_new(backend, 512, 512)
val pixels = make_4x4_rgba_pixels()
val packed = atlas_pack(atlas, backend, 200, pixels, 4, 4)
val found = atlas_lookup(atlas, 200)
expect(found.width).to_equal(packed.width)
expect(found.height).to_equal(packed.height)
```

</details>

#### AC-7: lookup unknown id returns zero-size rect

1. var backend = make software backend inited
   - Expected: found.width equals `0`
   - Expected: found.height equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
val atlas = atlas_new(backend, 512, 512)
val found = atlas_lookup(atlas, 9999)
expect(found.width).to_equal(0)
expect(found.height).to_equal(0)
```

</details>

### Stream F: material_bind

### material_bind calls correct texture slot bindings

#### AC-7: material_bind does not crash with valid albedo texture

1. var backend = make software backend inited
2. var cache = texture cache new
3. backend begin frame
4. material bind
5. backend end render pass
6. backend end frame
   - Expected: backend.active_pass.pass_id equals `-1`
   - Expected: backend.textures.length equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
var cache = texture_cache_new()
val pixels = make_2x2_rgba_pixels()
val tex_id = texture_cache_upload(cache, backend, 2, 2, TextureFormat3D.Rgba8Unorm, pixels)
val mat = Material3D.pbr_with_texture(tex_id)
backend.begin_frame()
val rph = make_render_pass(backend)
val desc = make_pipeline_desc()
val pip = backend.create_pipeline(desc)
material_bind(mat, cache, backend, rph)
backend.end_render_pass(rph)
backend.end_frame()
expect(backend.active_pass.pass_id).to_equal(-1)
expect(backend.textures.length).to_equal(3)
```

</details>

#### AC-7: material_bind with no texture does not crash

1. var backend = make software backend inited
2. var cache = texture cache new
3. backend begin frame
4. material bind
5. backend end render pass
6. backend end frame
   - Expected: backend.active_pass.pass_id equals `-1`
   - Expected: backend.textures.length equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = make_software_backend_inited()
var cache = texture_cache_new()
val mat = Material3D.phong()
backend.begin_frame()
val rph = make_render_pass(backend)
material_bind(mat, cache, backend, rph)
backend.end_render_pass(rph)
backend.end_frame()
expect(backend.active_pass.pass_id).to_equal(-1)
expect(backend.textures.length).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/engine/render/texture3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Stream F: TextureCache3D
- texture_cache_new
- texture_cache_upload
- texture_cache_get
- texture_cache_evict
- Stream F: TextureAtlas3D
- atlas_new
- atlas_pack
- atlas_lookup
- Stream F: material_bind
- material_bind calls correct texture slot bindings

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
