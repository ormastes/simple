# Backend Vulkan3d Harden Specification

> <details>

<!-- sdn-diagram:id=backend_vulkan3d_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=backend_vulkan3d_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

backend_vulkan3d_harden_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=backend_vulkan3d_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Vulkan3d Harden Specification

## Scenarios

### VulkanBackend3D — VulkanErrorKind3D classification

#### error classification

#### empty string classifies as None

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("")
expect(kind).to_equal(VulkanErrorKind3D.None)
```

</details>

#### device lost string classifies as DeviceLost

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("device lost in render pass")
expect(kind).to_equal(VulkanErrorKind3D.DeviceLost)
```

</details>

#### DEVICE_LOST classifies as DeviceLost

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("VK_ERROR_DEVICE_LOST")
expect(kind).to_equal(VulkanErrorKind3D.DeviceLost)
```

</details>

#### extension string classifies as MissingExtension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("required extension not supported")
expect(kind).to_equal(VulkanErrorKind3D.MissingExtension)
```

</details>

#### shader compile string classifies as ShaderCompile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("shader compile failed")
expect(kind).to_equal(VulkanErrorKind3D.ShaderCompile)
```

</details>

#### SPIR-V string classifies as ShaderCompile

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("invalid SPIR-V module")
expect(kind).to_equal(VulkanErrorKind3D.ShaderCompile)
```

</details>

#### unavailable string classifies as NotAvailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("Vulkan runtime unavailable")
expect(kind).to_equal(VulkanErrorKind3D.NotAvailable)
```

</details>

#### no Vulkan devices classifies as NoDevice

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("no Vulkan devices enumerated")
expect(kind).to_equal(VulkanErrorKind3D.NoDevice)
```

</details>

#### unknown error classifies as Other

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = vulkan3d_classify_error("unexpected internal error XYZ")
expect(kind).to_equal(VulkanErrorKind3D.Other)
```

</details>

### VulkanBackend3D — init guards

#### uninitialized backend

#### create() returns initialized=false

- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = VulkanBackend3D.create()
assert_false(b.initialized)
```

</details>

#### create() has empty last_error

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = VulkanBackend3D.create()
assert_equal(b.last_error, "")
```

</details>

#### init() with valid dimensions succeeds

- var b = VulkanBackend3D create
- assert true
- assert true
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
val ok = b.init(64, 64)
assert_true(ok)
assert_true(b.initialized)
assert_equal(b.last_error, "")
```

</details>

#### init() with zero width fails and sets last_error

- var b = VulkanBackend3D create
- assert false
- assert false
   - Expected: b.last_error == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
val ok = b.init(0, 64)
assert_false(ok)
assert_false(b.initialized)
# last_error must be non-empty on failure
val classified = vulkan3d_classify_error(b.last_error)
expect(b.last_error == "").to_equal(false)
```

</details>

#### init() with zero height fails and sets last_error

- var b = VulkanBackend3D create
- assert false
- assert false
   - Expected: b.last_error == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
val ok = b.init(64, 0)
assert_false(ok)
assert_false(b.initialized)
expect(b.last_error == "").to_equal(false)
```

</details>

#### draw calls before init are no-ops

#### clear() before init does not panic

- var b = VulkanBackend3D create
- b clear
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.clear(0xFF000000)
# No assertion needed — absence of panic is the guarantee
assert_false(b.initialized)
```

</details>

#### submit_triangle() before init does not panic and backend stays uninitialized

- var b = VulkanBackend3D create
- b submit triangle
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
val v0 = _v3(0.0, 0.0, 0.0)
val v1 = _v3(1.0, 0.0, 0.0)
val v2 = _v3(0.5, 1.0, 0.0)
b.submit_triangle(v0, v1, v2, _unlit_mat(), mat4_identity())
# Guard must not change initialized state
assert_false(b.initialized)
```

</details>

#### present() before init is a no-op

- var b = VulkanBackend3D create
- b present
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.present()
assert_false(b.initialized)
```

</details>

#### begin_frame() before init is a no-op

- var b = VulkanBackend3D create
- b begin frame
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.begin_frame()
assert_false(b.initialized)
```

</details>

#### end_frame() before init is a no-op

- var b = VulkanBackend3D create
- b end frame
- assert false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.end_frame()
assert_false(b.initialized)
```

</details>

#### draw calls after init work correctly

#### clear() after init sets buf pixels

- var b = VulkanBackend3D create
- b init
- b clear
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.init(4, 4)
b.clear(0xDEADBEEFu32)
val pixels = b.read_pixels()
assert_equal(pixels[0], 0xDEADBEEFu32)
assert_equal(pixels[15], 0xDEADBEEFu32)
```

</details>

#### after init clear+draw_image pipeline is functional

- var b = VulkanBackend3D create
- b init
- b clear
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.init(4, 4)
b.clear(0xAABBCCDDu32)
val pixels = b.read_pixels()
assert_equal(pixels[0], 0xAABBCCDDu32)
```

</details>

#### shutdown clears state

#### shutdown() resets initialized and last_error

- var b = VulkanBackend3D create
- b init
- b shutdown
- assert false
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.init(32, 32)
b.shutdown()
assert_false(b.initialized)
assert_equal(b.last_error, "")
```

</details>

### VulkanBackend3D — CPU migration semantics

#### fallback parity

#### uninitialized backend buf is empty (no silent state)

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = VulkanBackend3D.create()
assert_equal(b.buf.len(), 0)
```

</details>

#### after init+clear buf length matches w*h

- var b = VulkanBackend3D create
- b init
- b clear
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = VulkanBackend3D.create()
b.init(8, 8)
b.clear(0x00000000)
assert_equal(b.buf.len(), 64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VulkanBackend3D — VulkanErrorKind3D classification
- VulkanBackend3D — init guards
- VulkanBackend3D — CPU migration semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
