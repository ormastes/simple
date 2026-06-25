# Backend Metal3d Hardening Specification

> <details>

<!-- sdn-diagram:id=backend_metal3d_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_metal3d_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_metal3d_hardening_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_metal3d_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Metal3d Hardening Specification

## Scenarios

### Metal 3D backend — create and init

#### create() returns uninitialized backend

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = MetalBackend3D.create()
assert_false(b.initialized)
```

</details>

#### create() sets last_error to empty

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = MetalBackend3D.create()
assert_equal(b.last_error, "")
```

</details>

#### init() returns true (software fallback always succeeds)

- var b = MetalBackend3D create
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val result = b.init(64, 64)
assert_true(result)
```

</details>

#### initialized is true after init

- var b = MetalBackend3D create
- b init
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(64, 64)
assert_true(b.initialized)
```

</details>

#### last_error is empty after successful init

- var b = MetalBackend3D create
- b init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(64, 64)
assert_equal(b.last_error, "")
```

</details>

#### width() returns correct value after init

- var b = MetalBackend3D create
- b init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(64, 32)
assert_equal(b.width(), 64)
```

</details>

#### height() returns correct value after init

- var b = MetalBackend3D create
- b init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(64, 32)
assert_equal(b.height(), 32)
```

</details>

#### buf is sized w*h after init

- var b = MetalBackend3D create
- b init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(8, 8)
assert_equal(b.buf.len(), 64)
```

</details>

#### depth is sized w*h after init

- var b = MetalBackend3D create
- b init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(8, 8)
assert_equal(b.depth.len(), 64)
```

</details>

### Metal 3D backend — draw methods no-op when not initialized

#### clear() sets last_error when not initialized

- var b = MetalBackend3D create
- b clear
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.clear(0xFF0000FF)
assert_true(b.last_error.len() > 0)
```

</details>

#### clear_depth() sets last_error when not initialized

- var b = MetalBackend3D create
- b clear depth
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.clear_depth()
assert_true(b.last_error.len() > 0)
```

</details>

#### begin_frame() sets last_error when not initialized

- var b = MetalBackend3D create
- b begin frame
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.begin_frame()
assert_true(b.last_error.len() > 0)
```

</details>

#### submit_triangle() sets last_error when not initialized

- var b = MetalBackend3D create
- b submit triangle
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val v0 = _make_vertex(0.0, 0.0, 0.0)
val v1 = _make_vertex(1.0, 0.0, 0.0)
val v2 = _make_vertex(0.0, 1.0, 0.0)
val mat = _make_material()
val model = mat4_identity()
b.submit_triangle(v0, v1, v2, mat, model)
assert_true(b.last_error.len() > 0)
```

</details>

#### draw_image() sets last_error when not initialized

- var b = MetalBackend3D create
- b draw image
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val pixels: [u32] = [0xFF0000FFu32; 4]
b.draw_image(0, 0, 2, 2, pixels)
assert_true(b.last_error.len() > 0)
```

</details>

#### draw_cube() sets last_error when not initialized

- var b = MetalBackend3D create
- b draw cube
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val model = mat4_identity()
val mat = _make_material()
b.draw_cube(model, mat)
assert_true(b.last_error.len() > 0)
```

</details>

#### buf remains empty when draw called before init

- var b = MetalBackend3D create
- b clear
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.clear(0xFF0000FF)
assert_equal(b.buf.len(), 0)
```

</details>

### Metal 3D backend — read_pixels and read_depth before init

#### read_pixels() returns empty array before init

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = MetalBackend3D.create()
val pixels = b.read_pixels()
assert_equal(pixels.len(), 0)
```

</details>

#### read_depth() returns empty array before init

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = MetalBackend3D.create()
val depth = b.read_depth()
assert_equal(depth.len(), 0)
```

</details>

#### read_pixels() returns w*h pixels after init

- var b = MetalBackend3D create
- b init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(8, 8)
val pixels = b.read_pixels()
assert_equal(pixels.len(), 64)
```

</details>

#### read_depth() returns w*h depths after init

- var b = MetalBackend3D create
- b init
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(8, 8)
val depth = b.read_depth()
assert_equal(depth.len(), 64)
```

</details>

### Metal 3D backend — clear writes pixels after init

#### clear() fills buf with given color

- var b = MetalBackend3D create
- b init
- b clear
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(4, 4)
b.clear(0xDEADBEEFu32)
val pixels = b.read_pixels()
assert_equal(pixels[0], 0xDEADBEEFu32)
assert_equal(pixels[15], 0xDEADBEEFu32)
```

</details>

### Metal 3D backend — shutdown

#### shutdown sets initialized=false

- var b = MetalBackend3D create
- b init
- b shutdown
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(16, 16)
b.shutdown()
assert_false(b.initialized)
```

</details>

#### draw methods set last_error after shutdown

- var b = MetalBackend3D create
- b init
- b shutdown
- b clear
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.init(16, 16)
b.shutdown()
b.clear(0xFF0000FF)
assert_true(b.last_error.len() > 0)
```

</details>

### Metal 3D backend ext — init guards on extension methods

#### create_shader returns -1 when not initialized

- var b = MetalBackend3D create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val result = b.create_shader("", "")
assert_equal(result, -1)
```

</details>

#### create_pipeline returns -1 when not initialized

- var b = MetalBackend3D create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val result = b.create_pipeline(0, true, 0, 0)
assert_equal(result, -1)
```

</details>

#### create_storage_buffer returns -1 when not initialized

- var b = MetalBackend3D create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val result = b.create_storage_buffer(256)
assert_equal(result, -1)
```

</details>

#### read_buffer returns empty when not initialized

- var b = MetalBackend3D create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val result = b.read_buffer(0)
assert_equal(result.len(), 0)
```

</details>

#### occlusion_query returns -1 when not initialized

- var b = MetalBackend3D create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val result = b.occlusion_query(0, 0, 4, 4)
assert_equal(result, -1)
```

</details>

#### read_texture returns empty when not initialized

- var b = MetalBackend3D create
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
val result = b.read_texture(0, 0, 0)
assert_equal(result.len(), 0)
```

</details>

#### create_shader sets last_error when not initialized

- var b = MetalBackend3D create
- b create shader
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = MetalBackend3D.create()
b.create_shader("", "")
assert_true(b.last_error.len() > 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metal 3D backend — create and init
- Metal 3D backend — draw methods no-op when not initialized
- Metal 3D backend — read_pixels and read_depth before init
- Metal 3D backend — clear writes pixels after init
- Metal 3D backend — shutdown
- Metal 3D backend ext — init guards on extension methods

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
