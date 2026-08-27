# Backend Vulkan3d Harden Specification

> Tests covering VulkanBackend3D — VulkanErrorKind3D classification, VulkanBackend3D — init guards, VulkanBackend3D — CPU migration semantics.

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

- empty string classifies as None
   - Expected: kind equals `VulkanErrorKind3D.None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty string classifies as None")
val kind = vulkan3d_classify_error("")
expect(kind).to_equal(VulkanErrorKind3D.None)
```

</details>

#### device lost string classifies as DeviceLost

- device lost string classifies as DeviceLost
   - Expected: kind equals `VulkanErrorKind3D.DeviceLost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("device lost string classifies as DeviceLost")
val kind = vulkan3d_classify_error("device lost in render pass")
expect(kind).to_equal(VulkanErrorKind3D.DeviceLost)
```

</details>

#### DEVICE_LOST classifies as DeviceLost

- DEVICE_LOST classifies as DeviceLost
   - Expected: kind equals `VulkanErrorKind3D.DeviceLost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DEVICE_LOST classifies as DeviceLost")
val kind = vulkan3d_classify_error("VK_ERROR_DEVICE_LOST")
expect(kind).to_equal(VulkanErrorKind3D.DeviceLost)
```

</details>

#### extension string classifies as MissingExtension

- extension string classifies as MissingExtension
   - Expected: kind equals `VulkanErrorKind3D.MissingExtension`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extension string classifies as MissingExtension")
val kind = vulkan3d_classify_error("required extension not supported")
expect(kind).to_equal(VulkanErrorKind3D.MissingExtension)
```

</details>

#### shader compile string classifies as ShaderCompile

- shader compile string classifies as ShaderCompile
   - Expected: kind equals `VulkanErrorKind3D.ShaderCompile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shader compile string classifies as ShaderCompile")
val kind = vulkan3d_classify_error("shader compile failed")
expect(kind).to_equal(VulkanErrorKind3D.ShaderCompile)
```

</details>

#### SPIR-V string classifies as ShaderCompile

- SPIR-V string classifies as ShaderCompile
   - Expected: kind equals `VulkanErrorKind3D.ShaderCompile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SPIR-V string classifies as ShaderCompile")
val kind = vulkan3d_classify_error("invalid SPIR-V module")
expect(kind).to_equal(VulkanErrorKind3D.ShaderCompile)
```

</details>

#### unavailable string classifies as NotAvailable

- unavailable string classifies as NotAvailable
   - Expected: kind equals `VulkanErrorKind3D.NotAvailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unavailable string classifies as NotAvailable")
val kind = vulkan3d_classify_error("Vulkan runtime unavailable")
expect(kind).to_equal(VulkanErrorKind3D.NotAvailable)
```

</details>

#### no Vulkan devices classifies as NoDevice

- no Vulkan devices classifies as NoDevice
   - Expected: kind equals `VulkanErrorKind3D.NoDevice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no Vulkan devices classifies as NoDevice")
val kind = vulkan3d_classify_error("no Vulkan devices enumerated")
expect(kind).to_equal(VulkanErrorKind3D.NoDevice)
```

</details>

#### unknown error classifies as Other

- unknown error classifies as Other
   - Expected: kind equals `VulkanErrorKind3D.Other`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown error classifies as Other")
val kind = vulkan3d_classify_error("unexpected internal error XYZ")
expect(kind).to_equal(VulkanErrorKind3D.Other)
```

</details>

### VulkanBackend3D — init guards

#### uninitialized backend

#### create() returns initialized=false

- create() returns initialized=false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create() returns initialized=false")
val b = VulkanBackend3D.create()
assert_false(b.initialized)
```

</details>

#### create() has empty last_error

- create() has empty last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create() has empty last_error")
val b = VulkanBackend3D.create()
assert_equal(b.last_error, "")
```

</details>

#### init() with valid dimensions succeeds

- init() with valid dimensions succeeds


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init() with valid dimensions succeeds")
var b = VulkanBackend3D.create()
val ok = b.init(64, 64)
assert_true(ok)
assert_true(b.initialized)
assert_equal(b.last_error, "")
```

</details>

#### init() with zero width fails and sets last_error

- init() with zero width fails and sets last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init() with zero width fails and sets last_error")
var b = VulkanBackend3D.create()
val ok = b.init(0, 64)
assert_false(ok)
assert_false(b.initialized)
# last_error must be non-empty on failure
val classified = vulkan3d_classify_error(b.last_error)
expect(b.last_error).to_not_equal("")
```

</details>

#### init() with zero height fails and sets last_error

- init() with zero height fails and sets last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init() with zero height fails and sets last_error")
var b = VulkanBackend3D.create()
val ok = b.init(64, 0)
assert_false(ok)
assert_false(b.initialized)
expect(b.last_error).to_not_equal("")
```

</details>

#### draw calls before init are no-ops

#### clear() before init does not panic

- clear() before init does not panic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear() before init does not panic")
var b = VulkanBackend3D.create()
b.clear(0xFF000000)
# No assertion needed — absence of panic is the guarantee
assert_false(b.initialized)
```

</details>

#### submit_triangle() before init does not panic and backend stays uninitialized

- submit_triangle() before init does not panic and backend stays uninitialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submit_triangle() before init does not panic and backend stays uninitialized")
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

- present() before init is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("present() before init is a no-op")
var b = VulkanBackend3D.create()
b.present()
assert_false(b.initialized)
```

</details>

#### begin_frame() before init is a no-op

- begin_frame() before init is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("begin_frame() before init is a no-op")
var b = VulkanBackend3D.create()
b.begin_frame()
assert_false(b.initialized)
```

</details>

#### end_frame() before init is a no-op

- end_frame() before init is a no-op


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("end_frame() before init is a no-op")
var b = VulkanBackend3D.create()
b.end_frame()
assert_false(b.initialized)
```

</details>

#### draw calls after init work correctly

#### clear() after init sets buf pixels

- clear() after init sets buf pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear() after init sets buf pixels")
var b = VulkanBackend3D.create()
b.init(4, 4)
b.clear(0xDEADBEEFu32)
val pixels = b.read_pixels()
assert_equal(pixels[0], 0xDEADBEEFu32)
assert_equal(pixels[15], 0xDEADBEEFu32)
```

</details>

#### after init clear+draw_image pipeline is functional

- after init clear+draw_image pipeline is functional


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("after init clear+draw_image pipeline is functional")
var b = VulkanBackend3D.create()
b.init(4, 4)
b.clear(0xAABBCCDDu32)
val pixels = b.read_pixels()
assert_equal(pixels[0], 0xAABBCCDDu32)
```

</details>

#### shutdown clears state

#### shutdown() resets initialized and last_error

- shutdown() resets initialized and last_error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shutdown() resets initialized and last_error")
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

- uninitialized backend buf is empty (no silent state)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uninitialized backend buf is empty (no silent state)")
val b = VulkanBackend3D.create()
assert_equal(b.buf.len(), 0)
```

</details>

#### after init+clear buf length matches w*h

- after init+clear buf length matches w*h


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("after init+clear buf length matches w*h")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VulkanBackend3D — VulkanErrorKind3D classification, VulkanBackend3D — init guards, VulkanBackend3D — CPU migration semantics.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a6920042823227d311e74bc789b97ca6dd2f01245c1203b80362aba9111da67b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a6920042823227d311e74bc789b97ca6dd2f01245c1203b80362aba9111da67b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a6920042823227d311e74bc789b97ca6dd2f01245c1203b80362aba9111da67b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty string classifies as None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'device lost string classifies as DeviceLost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine3d/backend_vulkan3d_harden_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'DEVICE_LOST classifies as DeviceLost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
