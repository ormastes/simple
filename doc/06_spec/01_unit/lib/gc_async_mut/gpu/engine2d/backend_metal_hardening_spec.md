# Backend Metal Hardening Specification

> Tests covering Metal 2D backend — probe unavailable on non-macOS, Metal 2D backend — init guard on Linux, Metal 2D backend — draw methods are no-ops when not initialized, Metal 2D backend — read_pixels falls back to CPU mirror, Metal 2D backend — metal_classify_error all variants, MetalSession — error_message codes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Metal Hardening Specification

## Scenarios

### Metal 2D backend — probe unavailable on non-macOS

#### probe_metal returns available=false on Linux

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- probe_metal returns available=false on Linux


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_metal returns available=false on Linux")
val probe = probe_metal()
assert_false(probe.available)
```

</details>

#### probe_metal sets api_name to metal

- probe_metal sets api_name to metal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_metal sets api_name to metal")
val probe = probe_metal()
assert_equal(probe.api_name, "metal")
```

</details>

#### probe_metal sets shader_format to msl

- probe_metal sets shader_format to msl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_metal sets shader_format to msl")
val probe = probe_metal()
assert_equal(probe.shader_format, "msl")
```

</details>

#### probe_metal fallback_reason is non-empty

- probe_metal fallback_reason is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("probe_metal fallback_reason is non-empty")
val probe = probe_metal()
assert_true(probe.fallback_reason.len() > 0)
```

</details>

### Metal 2D backend — init guard on Linux

#### init() returns false on non-macOS

- init() returns false on non-macOS


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("init() returns false on non-macOS")
var b = make_metal_backend()
val result = b.init(64, 64)
assert_false(result)
```

</details>

#### initialized is false after failed init

- initialized is false after failed init


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initialized is false after failed init")
var b = make_metal_backend()
b.init(64, 64)
assert_false(b.initialized)
```

</details>

#### last_error is non-empty after failed init on Linux

- last_error is non-empty after failed init on Linux


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last_error is non-empty after failed init on Linux")
var b = make_metal_backend()
b.init(64, 64)
assert_true(b.last_error.len() > 0)
```

</details>

#### last_error contains Metal on Linux init failure

- last_error contains Metal on Linux init failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("last_error contains Metal on Linux init failure")
var b = make_metal_backend()
b.init(64, 64)
assert_true(b.last_error.contains("Metal"))
```

</details>

### Metal 2D backend — draw methods are no-ops when not initialized

#### clear() leaves gpu_frame_complete false when not initialized

- clear() leaves gpu_frame_complete false when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear() leaves gpu_frame_complete false when not initialized")
var b = make_metal_backend()
b.clear(0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_rect() leaves gpu_frame_complete false when not initialized

- draw_rect() leaves gpu_frame_complete false when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_rect() leaves gpu_frame_complete false when not initialized")
var b = make_metal_backend()
b.draw_rect(0, 0, 10, 10, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_rect_filled() leaves gpu_frame_complete false when not initialized

- draw_rect_filled() leaves gpu_frame_complete false when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_rect_filled() leaves gpu_frame_complete false when not initialized")
var b = make_metal_backend()
b.draw_rect_filled(0, 0, 10, 10, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_line() leaves gpu_frame_complete false when not initialized

- draw_line() leaves gpu_frame_complete false when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_line() leaves gpu_frame_complete false when not initialized")
var b = make_metal_backend()
b.draw_line(0, 0, 10, 10, 0xFF0000FF, 1)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_circle() leaves gpu_frame_complete false when not initialized

- draw_circle() leaves gpu_frame_complete false when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_circle() leaves gpu_frame_complete false when not initialized")
var b = make_metal_backend()
b.draw_circle(5, 5, 4, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### draw_triangle_filled() leaves gpu_frame_complete false when not initialized

- draw_triangle_filled() leaves gpu_frame_complete false when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_triangle_filled() leaves gpu_frame_complete false when not initialized")
var b = make_metal_backend()
b.draw_triangle_filled(0, 0, 10, 0, 5, 10, 0xFF0000FF)
assert_false(b.gpu_frame_complete)
```

</details>

#### clear() sets last_error when not initialized

- clear() sets last_error when not initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clear() sets last_error when not initialized")
var b = make_metal_backend()
b.clear(0xFF0000FF)
assert_true(b.last_error.len() > 0)
```

</details>

### Metal 2D backend — read_pixels falls back to CPU mirror

#### read_pixels returns non-empty array after init failure (mirror fallback)

- read_pixels returns non-empty array after init failure (mirror fallback)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read_pixels returns non-empty array after init failure (mirror fallback)")
var b = make_metal_backend()
b.init(8, 8)
# Mirror is always initialized (SoftwareBackend)
b.mirror.init(8, 8)
b.mirror.clear(0xFF112233)
val pixels = b.read_pixels()
# Falls back to mirror since gpu_frame_complete=false
assert_true(pixels.len() > 0)
```

</details>

#### width() delegates to mirror when uninitialized

- width() delegates to mirror when uninitialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("width() delegates to mirror when uninitialized")
var b = make_metal_backend()
b.mirror.init(16, 32)
val w = b.width()
assert_equal(w, 16)
```

</details>

#### height() delegates to mirror when uninitialized

- height() delegates to mirror when uninitialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("height() delegates to mirror when uninitialized")
var b = make_metal_backend()
b.mirror.init(16, 32)
val h = b.height()
assert_equal(h, 32)
```

</details>

### Metal 2D backend — metal_classify_error all variants

#### classifies not-available message as NotAvailable

- classifies not-available message as NotAvailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies not-available message as NotAvailable")
val kind = metal_classify_error("Metal SFFI not available")
assert_equal(kind, MetalErrorKind.NotAvailable)
```

</details>

#### classifies device creation message as DeviceLost

- classifies device creation message as DeviceLost


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies device creation message as DeviceLost")
val kind = metal_classify_error("Metal device creation failed")
assert_equal(kind, MetalErrorKind.DeviceLost)
```

</details>

#### classifies shader compilation message as ShaderCompile

- classifies shader compilation message as ShaderCompile


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies shader compilation message as ShaderCompile")
val kind = metal_classify_error("Metal shader compilation failed")
assert_equal(kind, MetalErrorKind.ShaderCompile)
```

</details>

#### classifies no devices message as NoDevice

- classifies no devices message as NoDevice


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies no devices message as NoDevice")
val kind = metal_classify_error("No Metal devices found")
assert_equal(kind, MetalErrorKind.NoDevice)
```

</details>

#### classifies pipeline message as PipelineCreate

- classifies pipeline message as PipelineCreate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies pipeline message as PipelineCreate")
val kind = metal_classify_error("Metal compute pipeline creation failed")
assert_equal(kind, MetalErrorKind.PipelineCreate)
```

</details>

#### classifies alloc message as AllocFailed

- classifies alloc message as AllocFailed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies alloc message as AllocFailed")
val kind = metal_classify_error("Metal framebuffer allocation failed")
assert_equal(kind, MetalErrorKind.AllocFailed)
```

</details>

#### classifies mirror message as AllocFailed

- classifies mirror message as AllocFailed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies mirror message as AllocFailed")
val kind = metal_classify_error("Metal mirror surface allocation failed")
assert_equal(kind, MetalErrorKind.AllocFailed)
```

</details>

#### classifies unknown message as Other

- classifies unknown message as Other


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies unknown message as Other")
val kind = metal_classify_error("unexpected gpu error XYZ")
assert_equal(kind, MetalErrorKind.Other)
```

</details>

#### classifies empty string as None

- classifies empty string as None


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies empty string as None")
val kind = metal_classify_error("")
assert_equal(kind, MetalErrorKind.None)
```

</details>

### MetalSession — error_message codes

#### error_message returns empty string for code 0 (success)

- error_message returns empty string for code 0 (success)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns empty string for code 0 (success)")
var s = MetalSession.create("test")
s.last_error = 0
assert_equal(s.error_message(), "")
```

</details>

#### error_message returns non-empty for code 1 (SFFI unavailable)

- error_message returns non-empty for code 1 (SFFI unavailable)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns non-empty for code 1 (SFFI unavailable)")
var s = MetalSession.create("test")
s.last_error = 1
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 2 (runtime init failed)

- error_message returns non-empty for code 2 (runtime init failed)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns non-empty for code 2 (runtime init failed)")
var s = MetalSession.create("test")
s.last_error = 2
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 3 (no devices)

- error_message returns non-empty for code 3 (no devices)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns non-empty for code 3 (no devices)")
var s = MetalSession.create("test")
s.last_error = 3
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 4 (device create)

- error_message returns non-empty for code 4 (device create)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns non-empty for code 4 (device create)")
var s = MetalSession.create("test")
s.last_error = 4
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 5 (queue create)

- error_message returns non-empty for code 5 (queue create)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns non-empty for code 5 (queue create)")
var s = MetalSession.create("test")
s.last_error = 5
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 6 (shader compile)

- error_message returns non-empty for code 6 (shader compile)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns non-empty for code 6 (shader compile)")
var s = MetalSession.create("test")
s.last_error = 6
assert_true(s.error_message().len() > 0)
```

</details>

#### error_message returns non-empty for code 7 (pipeline create)

- error_message returns non-empty for code 7 (pipeline create)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_message returns non-empty for code 7 (pipeline create)")
var s = MetalSession.create("test")
s.last_error = 7
assert_true(s.error_message().len() > 0)
```

</details>

#### error_code() returns 0 on fresh session

- error_code() returns 0 on fresh session


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error_code() returns 0 on fresh session")
var s = MetalSession.create("test")
assert_equal(s.error_code(), 0)
```

</details>

#### font composite dispatch rejects invalid ABI inputs before SFFI

- font composite dispatch rejects invalid ABI inputs before SFFI


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("font composite dispatch rejects invalid ABI inputs before SFFI")
var s = MetalSession.create("test")
s.device = 1
s.command_queue = 1
s.pipe_font_atlas_composite = 1
s.is_initialized = true
val exact: [u8] = [0u8; 52]
val short: [u8] = [0u8; 51]
assert_false(s.dispatch_font_atlas_composite(1, 2, short, 1))
assert_false(s.dispatch_font_atlas_composite(0, 2, exact, 1))
assert_false(s.dispatch_font_atlas_composite(1, 2, exact, 0))
assert_false(s.dispatch_font_atlas_composite(1, 2, exact, 2147483648))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Metal 2D backend — probe unavailable on non-macOS, Metal 2D backend — init guard on Linux, Metal 2D backend — draw methods are no-ops when not initialized, Metal 2D backend — read_pixels falls back to CPU mirror, Metal 2D backend — metal_classify_error all variants, MetalSession — error_message codes.
- Metal 2D backend — probe unavailable on non-macOS
- Metal 2D backend — init guard on Linux
- Metal 2D backend — draw methods are no-ops when not initialized
- Metal 2D backend — read_pixels falls back to CPU mirror
- Metal 2D backend — metal_classify_error all variants
- MetalSession — error_message codes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
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

- Canonical SPipe generation for source `db22f289558801bb617279a24727e02b99f829c0ec7185553d7a5a82c9ed7dbd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db22f289558801bb617279a24727e02b99f829c0ec7185553d7a5a82c9ed7dbd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db22f289558801bb617279a24727e02b99f829c0ec7185553d7a5a82c9ed7dbd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_metal returns available=false on Linux' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_metal sets api_name to metal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_metal_hardening_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'probe_metal sets shader_format to msl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
