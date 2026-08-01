# Resource Pool Specification

> <details>

<!-- sdn-diagram:id=resource_pool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_pool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_pool_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_pool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resource Pool Specification

## Scenarios

### Engine3D ResourcePool3D

#### ResourcePool3D.create

#### total_resource_count starts at 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pool = ResourcePool3D.create()
expect(pool.total_resource_count()).to_equal(0)
```

</details>

#### allocate_texture

#### returns handle with correct width

- var pool = ResourcePool3D create
   - Expected: h.width equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(512, 256, 1, TEX_FMT_RGBA8_UNORM, 1, 42)
expect(h.width).to_equal(512)
```

</details>

#### returns handle with correct height

- var pool = ResourcePool3D create
   - Expected: h.height equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(512, 256, 1, TEX_FMT_RGBA8_UNORM, 1, 42)
expect(h.height).to_equal(256)
```

</details>

#### returns handle with correct depth

- var pool = ResourcePool3D create
   - Expected: h.depth equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(512, 256, 4, TEX_FMT_RGBA8_UNORM, 1, 42)
expect(h.depth).to_equal(4)
```

</details>

#### texture_count increments

- var pool = ResourcePool3D create
- pool allocate texture
   - Expected: pool.texture_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 1)
expect(pool.texture_count()).to_equal(1)
```

</details>

#### allocate_buffer

#### buffer_count increments

- var pool = ResourcePool3D create
- pool allocate buffer
   - Expected: pool.buffer_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
pool.allocate_buffer(1024, 0, 1)
expect(pool.buffer_count()).to_equal(1)
```

</details>

#### allocate_shader

#### shader_count increments

- var pool = ResourcePool3D create
- pool allocate shader
   - Expected: pool.shader_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
pool.allocate_shader("vs_main", "fs_main", 1)
expect(pool.shader_count()).to_equal(1)
```

</details>

#### allocate_pipeline

#### pipeline_count increments

- var pool = ResourcePool3D create
- pool allocate pipeline
   - Expected: pool.pipeline_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
pool.allocate_pipeline(1, true, 0, 0, 1)
expect(pool.pipeline_count()).to_equal(1)
```

</details>

#### free_texture

#### texture_count decrements

- var pool = ResourcePool3D create
- pool free texture
   - Expected: pool.texture_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 1)
pool.free_texture(h.id)
expect(pool.texture_count()).to_equal(0)
```

</details>

#### find_texture

#### returns handle for valid id

- var pool = ResourcePool3D create
   - Expected: h.width equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(128, 128, 1, TEX_FMT_RGBA8_UNORM, 1, 5)
expect(h.width).to_equal(128)
```

</details>

#### returns nil for invalid id

- var pool = ResourcePool3D create
   - Expected: found.is_nil() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val found = pool.find_texture(99999)
expect(found.is_nil()).to_equal(true)
```

</details>

#### touch_texture

#### updates last_used_frame after advance_frame

- var pool = ResourcePool3D create
- pool advance frame
- pool touch texture
- pool advance frame
- pool advance frame
   - Expected: freed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 1)
pool.advance_frame()
pool.touch_texture(h.id)
pool.advance_frame()
pool.advance_frame()
val freed = pool.gc_unused_textures(2)
expect(freed).to_equal(0)
```

</details>

#### gc_unused_textures

#### removes old textures

- var pool = ResourcePool3D create
- pool allocate texture
- pool advance frame
- pool advance frame
- pool advance frame
   - Expected: freed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 1)
pool.advance_frame()
pool.advance_frame()
pool.advance_frame()
val freed = pool.gc_unused_textures(2)
expect(freed).to_equal(1)
```

</details>

#### keeps fresh textures

- var pool = ResourcePool3D create
- pool advance frame
- pool touch texture
   - Expected: freed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 1)
pool.advance_frame()
pool.touch_texture(h.id)
val freed = pool.gc_unused_textures(2)
expect(freed).to_equal(0)
```

</details>

#### gpu_id field

#### allocated handle has correct gpu_id

- var pool = ResourcePool3D create
   - Expected: h.gpu_id equals `77`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
val h = pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 77)
expect(h.gpu_id).to_equal(77)
```

</details>

#### gc_unused combined

#### returns total freed count

- var pool = ResourcePool3D create
- pool allocate texture
- pool allocate buffer
- pool advance frame
- pool advance frame
- pool advance frame
   - Expected: freed equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 1)
pool.allocate_buffer(256, 0, 1)
pool.advance_frame()
pool.advance_frame()
pool.advance_frame()
val freed = pool.gc_unused(2)
expect(freed).to_equal(2)
```

</details>

#### total_resource_count

#### sums all resource types

- var pool = ResourcePool3D create
- pool allocate texture
- pool allocate buffer
- pool allocate shader
- pool allocate pipeline
   - Expected: pool.total_resource_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = ResourcePool3D.create()
pool.allocate_texture(64, 64, 1, TEX_FMT_RGBA8_UNORM, 1, 1)
pool.allocate_buffer(256, 0, 1)
pool.allocate_shader("vs", "fs", 1)
pool.allocate_pipeline(1, false, 0, 0, 1)
expect(pool.total_resource_count()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/resource_pool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D ResourcePool3D

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
