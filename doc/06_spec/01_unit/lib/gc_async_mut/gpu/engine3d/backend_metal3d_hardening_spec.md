# Backend Metal3d Hardening Specification

> Tests covering Metal 3D backend — create and init, Metal 3D backend — draw methods no-op when not initialized, Metal 3D backend — read_pixels and read_depth before init, Metal 3D backend — clear writes pixels after init, Metal 3D backend — shutdown, Metal 3D backend ext — init guards on extension methods.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Metal3d Hardening Specification

## Scenarios

### Metal 3D backend — create and init

#### create() returns uninitialized backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create() returns uninitialized backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create() returns uninitialized backend")
val b = MetalBackend3D.create()
assert_false(b.initialized)
```

</details>

#### create() sets last_error to empty

- create() sets last_error to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create() sets last_error to empty")
val b = MetalBackend3D.create()
assert_equal(b.last_error, "")
```

</details>

#### init() returns true (software fallback always succeeds)

- init() returns true (software fallback always succeeds)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init() returns true (software fallback always succeeds)")
var b = MetalBackend3D.create()
val result = b.init(64, 64)
assert_true(result)
```

</details>

#### initialized is true after init

- initialized is true after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initialized is true after init")
var b = MetalBackend3D.create()
b.init(64, 64)
assert_true(b.initialized)
```

</details>

#### last_error is empty after successful init

- last_error is empty after successful init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last_error is empty after successful init")
var b = MetalBackend3D.create()
b.init(64, 64)
assert_equal(b.last_error, "")
```

</details>

#### width() returns correct value after init

- width() returns correct value after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("width() returns correct value after init")
var b = MetalBackend3D.create()
b.init(64, 32)
assert_equal(b.width(), 64)
```

</details>

#### height() returns correct value after init

- height() returns correct value after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("height() returns correct value after init")
var b = MetalBackend3D.create()
b.init(64, 32)
assert_equal(b.height(), 32)
```

</details>

#### buf is sized w*h after init

- buf is sized w*h after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("buf is sized w*h after init")
var b = MetalBackend3D.create()
b.init(8, 8)
assert_equal(b.buf.len(), 64)
```

</details>

#### depth is sized w*h after init

- depth is sized w*h after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("depth is sized w*h after init")
var b = MetalBackend3D.create()
b.init(8, 8)
assert_equal(b.depth.len(), 64)
```

</details>

### Metal 3D backend — draw methods no-op when not initialized

#### clear() sets last_error when not initialized

- clear() sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear() sets last_error when not initialized")
var b = MetalBackend3D.create()
b.clear(0xFF0000FF)
assert_true(b.last_error.len() > 0)
```

</details>

#### clear_depth() sets last_error when not initialized

- clear_depth() sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear_depth() sets last_error when not initialized")
var b = MetalBackend3D.create()
b.clear_depth()
assert_true(b.last_error.len() > 0)
```

</details>

#### begin_frame() sets last_error when not initialized

- begin_frame() sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("begin_frame() sets last_error when not initialized")
var b = MetalBackend3D.create()
b.begin_frame()
assert_true(b.last_error.len() > 0)
```

</details>

#### submit_triangle() sets last_error when not initialized

- submit_triangle() sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submit_triangle() sets last_error when not initialized")
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

- draw_image() sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_image() sets last_error when not initialized")
var b = MetalBackend3D.create()
val pixels: [u32] = [0xFF0000FFu32; 4]
b.draw_image(0, 0, 2, 2, pixels)
assert_true(b.last_error.len() > 0)
```

</details>

#### draw_cube() sets last_error when not initialized

- draw_cube() sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_cube() sets last_error when not initialized")
var b = MetalBackend3D.create()
val model = mat4_identity()
val mat = _make_material()
b.draw_cube(model, mat)
assert_true(b.last_error.len() > 0)
```

</details>

#### buf remains empty when draw called before init

- buf remains empty when draw called before init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("buf remains empty when draw called before init")
var b = MetalBackend3D.create()
b.clear(0xFF0000FF)
assert_equal(b.buf.len(), 0)
```

</details>

### Metal 3D backend — read_pixels and read_depth before init

#### read_pixels() returns empty array before init

- read_pixels() returns empty array before init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_pixels() returns empty array before init")
val b = MetalBackend3D.create()
val pixels = b.read_pixels()
assert_equal(pixels.len(), 0)
```

</details>

#### read_depth() returns empty array before init

- read_depth() returns empty array before init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_depth() returns empty array before init")
val b = MetalBackend3D.create()
val depth = b.read_depth()
assert_equal(depth.len(), 0)
```

</details>

#### read_pixels() returns w*h pixels after init

- read_pixels() returns w*h pixels after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_pixels() returns w*h pixels after init")
var b = MetalBackend3D.create()
b.init(8, 8)
val pixels = b.read_pixels()
assert_equal(pixels.len(), 64)
```

</details>

#### read_depth() returns w*h depths after init

- read_depth() returns w*h depths after init


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_depth() returns w*h depths after init")
var b = MetalBackend3D.create()
b.init(8, 8)
val depth = b.read_depth()
assert_equal(depth.len(), 64)
```

</details>

### Metal 3D backend — clear writes pixels after init

#### clear() fills buf with given color

- clear() fills buf with given color


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear() fills buf with given color")
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

- shutdown sets initialized=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shutdown sets initialized=false")
var b = MetalBackend3D.create()
b.init(16, 16)
b.shutdown()
assert_false(b.initialized)
```

</details>

#### draw methods set last_error after shutdown

- draw methods set last_error after shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw methods set last_error after shutdown")
var b = MetalBackend3D.create()
b.init(16, 16)
b.shutdown()
b.clear(0xFF0000FF)
assert_true(b.last_error.len() > 0)
```

</details>

### Metal 3D backend ext — init guards on extension methods

#### create_shader returns -1 when not initialized

- create_shader returns -1 when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_shader returns -1 when not initialized")
var b = MetalBackend3D.create()
val result = b.create_shader("", "")
assert_equal(result, -1)
```

</details>

#### create_pipeline returns -1 when not initialized

- create_pipeline returns -1 when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_pipeline returns -1 when not initialized")
var b = MetalBackend3D.create()
val result = b.create_pipeline(0, true, 0, 0)
assert_equal(result, -1)
```

</details>

#### create_storage_buffer returns -1 when not initialized

- create_storage_buffer returns -1 when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_storage_buffer returns -1 when not initialized")
var b = MetalBackend3D.create()
val result = b.create_storage_buffer(256)
assert_equal(result, -1)
```

</details>

#### read_buffer returns empty when not initialized

- read_buffer returns empty when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_buffer returns empty when not initialized")
var b = MetalBackend3D.create()
val result = b.read_buffer(0)
assert_equal(result.len(), 0)
```

</details>

#### occlusion_query returns -1 when not initialized

- occlusion_query returns -1 when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("occlusion_query returns -1 when not initialized")
var b = MetalBackend3D.create()
val result = b.occlusion_query(0, 0, 4, 4)
assert_equal(result, -1)
```

</details>

#### read_texture returns empty when not initialized

- read_texture returns empty when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_texture returns empty when not initialized")
var b = MetalBackend3D.create()
val result = b.read_texture(0, 0, 0)
assert_equal(result.len(), 0)
```

</details>

#### create_shader sets last_error when not initialized

- create_shader sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create_shader sets last_error when not initialized")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Metal 3D backend — create and init, Metal 3D backend — draw methods no-op when not initialized, Metal 3D backend — read_pixels and read_depth before init, Metal 3D backend — clear writes pixels after init, Metal 3D backend — shutdown, Metal 3D backend ext — init guards on extension methods.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e9045fbc1595b2a7afa6da95ad851e9e14b252a7d727d3e3412615587220034`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e9045fbc1595b2a7afa6da95ad851e9e14b252a7d727d3e3412615587220034`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e9045fbc1595b2a7afa6da95ad851e9e14b252a7d727d3e3412615587220034`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create() returns uninitialized backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create() sets last_error to empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_metal3d_hardening_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'init() returns true (software fallback always succeeds)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
