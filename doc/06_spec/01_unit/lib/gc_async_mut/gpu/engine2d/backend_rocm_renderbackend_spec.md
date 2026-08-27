# Backend Rocm Renderbackend Specification

> Tests covering RocmBackend init guards, RocmBackend draw-method init guards (GPU-less), RocmBackend read_pixels and present guards (GPU-less), RocmBackend probe error classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Rocm Renderbackend Specification

## Scenarios

### RocmBackend init guards

#### exports device identity through both async ROCm facades

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports device identity through both async ROCm facades


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports device identity through both async ROCm facades")
val no_gc = file_read("src/lib/nogc_async_mut/io/rocm_sffi.spl")
val gc = file_read("src/lib/gc_async_mut/io/rocm_sffi.spl")
val runtime = file_read("src/runtime/runtime_rocm.c")
expect(no_gc).to_contain("rt_rocm_device_identity")
expect(gc).to_contain("rt_rocm_device_identity")
expect(runtime).to_contain("hash &= ((uint64_t)INT64_MAX >> 3)")
```

</details>

#### bounds framebuffer multiplication before device or host allocation

- bounds framebuffer multiplication before device or host allocation
   - Expected: rocm_framebuffer_pixel_count(10000, 10000) equals `100000000`
   - Expected: rocm_framebuffer_pixel_count(10000, 10001) equals `0`
   - Expected: rocm_framebuffer_pixel_count(65536, 65536) equals `0`
   - Expected: rocm_framebuffer_pixel_count(0, 64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds framebuffer multiplication before device or host allocation")
expect(rocm_framebuffer_pixel_count(10000, 10000)).to_equal(100000000)
expect(rocm_framebuffer_pixel_count(10000, 10001)).to_equal(0)
expect(rocm_framebuffer_pixel_count(65536, 65536)).to_equal(0)
expect(rocm_framebuffer_pixel_count(0, 64)).to_equal(0)
```

</details>

#### create() yields initialized=false without AMD hardware

- create() yields initialized=false without AMD hardware
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create() yields initialized=false without AMD hardware")
var b = RocmBackend.create()
expect(b.initialized).to_equal(false)
```

</details>

#### create() sets last_probe to not-probed before init

- create() sets last_probe to not-probed before init
   - Expected: b.last_probe.requested_name equals `rocm`
   - Expected: b.last_probe.status equals `BackendStatus.Unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("create() sets last_probe to not-probed before init")
var b = RocmBackend.create()
expect(b.last_probe.requested_name).to_equal("rocm")
expect(b.last_probe.status).to_equal(BackendStatus.Unavailable)
```

</details>

#### init() on a GPU-less host returns false

- init() on a GPU-less host returns false
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("init() on a GPU-less host returns false")
var b = RocmBackend.create()
val ok = b.init(64, 64)
expect(ok).to_equal(false)
```

</details>

#### after failed init last_probe carries a non-empty feature_gate

- after failed init last_probe carries a non-empty feature_gate
   - Expected: has_gate is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("after failed init last_probe carries a non-empty feature_gate")
var b = RocmBackend.create()
b.init(64, 64)
val has_gate = b.last_probe.feature_gate != ""
expect(has_gate).to_equal(true)
```

</details>

#### after failed init last_probe carries a non-empty reason

- after failed init last_probe carries a non-empty reason
   - Expected: has_reason is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("after failed init last_probe carries a non-empty reason")
var b = RocmBackend.create()
b.init(64, 64)
val has_reason = b.last_probe.reason != ""
expect(has_reason).to_equal(true)
```

</details>

#### after failed init last_probe.api_name is rocm

- after failed init last_probe.api_name is rocm
   - Expected: b.last_probe.api_name equals `rocm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("after failed init last_probe.api_name is rocm")
var b = RocmBackend.create()
b.init(64, 64)
expect(b.last_probe.api_name).to_equal("rocm")
```

</details>

#### after failed init last_probe.shader_format is hsaco

- after failed init last_probe.shader_format is hsaco
   - Expected: b.last_probe.shader_format equals `hsaco`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("after failed init last_probe.shader_format is hsaco")
var b = RocmBackend.create()
b.init(64, 64)
expect(b.last_probe.shader_format).to_equal("hsaco")
```

</details>

### RocmBackend draw-method init guards (GPU-less)

#### packs the frozen 15-slot font ABI in kernel order

- packs the frozen 15-slot font ABI in kernel order


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("packs the frozen 15-slot font ABI in kernel order")
expect(rocm_font_atlas_composite_args(
    0x12345678, 0x23456789, 1024, 512, 524288,
    11, 12, 31, 32, 800, 600, 480000, -17, -19, 0xF1020304
)).to_equal([
    0x12345678, 0x23456789, 1024, 512, 524288,
    11, 12, 31, 32, 800, 600, 480000, -17, -19, 0xF1020304
])
```

</details>

#### keeps ROCm font cache failure and shutdown ordering fail closed

- keeps ROCm font cache failure and shutdown ordering fail closed
   - Expected: source.index_of("if (self.font_artifact_sha256 == \"\"") < source.index_of("sha256_text(_engine2d_hip_source())") is true
   - Expected: source.split("sha256_text(_engine2d_hip_source())").len() equals `2`
   - Expected: source does not contain `val artifact_identity = if self.hip_module > 0 and self.fn_font_atlas_composi... (full value in folded executable source)`
   - Expected: source.index_of("if rocm_engine2d_upload_pixels(target") < source.index_of("rocm_backend_free(self.d_font_atlas)") is true
   - Expected: source.index_of("if not _launch_kernel_1d(self, self.fn_font_atlas_composite") < source.index_of("if not rocm_backend_synchronize()") is true
   - Expected: source.index_of("if not rocm_backend_synchronize()") < source.index_of("self.dirty = true") is true
   - Expected: source.index_of("self.dirty = true") < source.index_of("submitted = submitted + 1") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps ROCm font cache failure and shutdown ordering fail closed")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_rocm.spl")
val runtime = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_rocm_runtime_ops.spl")
expect(source).to_contain("font_atlas_composite_cache_identity(")
expect(source).to_contain("font_render_batch_atlas_owner_identity(batch), \"rocm\", device_features")
expect(source).to_contain("if (self.font_artifact_sha256 == \"\" and self.hip_module > 0")
expect(source.index_of("if (self.font_artifact_sha256 == \"\"") < source.index_of("sha256_text(_engine2d_hip_source())")).to_equal(true)
expect(source.split("sha256_text(_engine2d_hip_source())").len()).to_equal(2)
expect(source).to_contain("\"source-sha256=\" + self.font_artifact_sha256")
expect(source).to_contain("artifact_identity, dependency_identity")
expect(source).to_contain("self.font_artifact_sha256 = \"\"")
expect(source.contains("val artifact_identity = if self.hip_module > 0 and self.fn_font_atlas_composite > 0:\n            \"module=\"")).to_equal(false)
expect(source).to_contain("self.font_atlas_owner_identity == owner_identity and self.font_atlas_generation == batch.atlas_generation")
expect(source.index_of("if rocm_engine2d_upload_pixels(target") < source.index_of("rocm_backend_free(self.d_font_atlas)")).to_equal(true)
expect(source).to_contain("if not _launch_kernel_1d(self, self.fn_font_atlas_composite, grid_size, 256, args):\n                return submitted")
expect(source).to_contain("if not rocm_backend_synchronize():\n                return submitted")
expect(source.index_of("if not _launch_kernel_1d(self, self.fn_font_atlas_composite") < source.index_of("if not rocm_backend_synchronize()")).to_equal(true)
expect(source.index_of("if not rocm_backend_synchronize()") < source.index_of("self.dirty = true")).to_equal(true)
expect(source.index_of("self.dirty = true") < source.index_of("submitted = submitted + 1")).to_equal(true)
expect(source).to_contain("me shutdown():\n        if self.d_font_atlas != 0:\n            rocm_backend_free(self.d_font_atlas)\n            self.d_font_atlas = 0\n        self.font_atlas_bytes = 0\n        self.invalidate_font_atlas()")
expect(runtime).to_contain("pub fn rocm_backend_synchronize() -> bool:")
expect(runtime).to_contain("pub fn rocm_backend_launch_kernel(func: i64")
expect(runtime).to_contain("args: [i64]) -> bool:")
```

</details>

#### fails closed when ROCm framebuffer transfer or identity evidence is unavailable

- fails closed when ROCm framebuffer transfer or identity evidence is unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed when ROCm framebuffer transfer or identity evidence is unavailable")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_rocm.spl")
val runtime = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_rocm_runtime_ops.spl")
expect(source).to_contain("if not _download_framebuffer(self.d_framebuffer, self.host_buf, fb_size) or not rocm_backend_synchronize():")
expect(source).to_contain("self.completion_unknown = true")
expect(source).to_contain("return engine2d_readback([], \"completion_unknown\")")
expect(source).to_contain("engine2d_readback_with_identity(copy, source, self.d_framebuffer, self.device_identity)")
expect(source).to_contain("if self.device_identity <= 0:")
expect(runtime).to_contain("rt_rocm_device_identity(device)")
expect(source).to_contain("_rocm_probe_ready(device_name)")
expect(source).to_contain("if device_name == \"\" or device_memory <= 0:")
expect(source).to_contain("if not rocm_backend_memset(self.d_framebuffer, 0, fb_size):")
expect(source).to_contain("if self.host_buf.len() != _i64(total):")
expect(source).to_contain("if copy.len() != _i64(self.pixel_count):\n            return engine2d_readback([], \"completion_unknown\")")
expect(source).to_contain("if not _upload_pixels_to_device(d_src, pixels, pixel_count):")
expect(source).to_contain("if not rocm_backend_synchronize():\n        backend.completion_unknown = true")
```

</details>

#### invalidates reusable ROCm atlas metadata without hardware

- invalidates reusable ROCm atlas metadata without hardware
   - Expected: b.font_atlas_bytes equals `64`
   - Expected: b.font_atlas_generation equals `-1`
   - Expected: b.font_atlas_owner_identity equals ``
   - Expected: b.d_font_atlas equals `0`
   - Expected: b.font_atlas_bytes equals `0`
   - Expected: b.font_atlas_generation equals `-1`
   - Expected: b.font_atlas_owner_identity equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("invalidates reusable ROCm atlas metadata without hardware")
var b = RocmBackend.create()
b.font_atlas_bytes = 64
b.font_atlas_generation = 7
b.font_atlas_owner_identity = "old-owner"
b.invalidate_font_atlas()
expect(b.font_atlas_bytes).to_equal(64)
expect(b.font_atlas_generation).to_equal(-1)
expect(b.font_atlas_owner_identity).to_equal("")
b.shutdown()
expect(b.d_font_atlas).to_equal(0)
expect(b.font_atlas_bytes).to_equal(0)
expect(b.font_atlas_generation).to_equal(-1)
expect(b.font_atlas_owner_identity).to_equal("")
```

</details>

#### emits C++ comments instead of invalid HIP preprocessor directives

- emits C++ comments instead of invalid HIP preprocessor directives
   - Expected: _has_invalid_hip_hash_comment(source) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits C++ comments instead of invalid HIP preprocessor directives")
val source = _engine2d_hip_source()
expect(source).to_contain("#include <hip/hip_runtime.h>")
expect(source).to_contain("// kernel_clear:")
expect(_has_invalid_hip_hash_comment(source)).to_equal(false)
```

</details>

#### kernel_draw_gradient_rect interpolates channels as signed int, not unsigned (descending-channel gradients must not wrap)

- kernel_draw_gradient_rect interpolates channels as signed int, not unsigned (descending-channel gradients must not wrap)
   - Expected: gradient_start >= 0 is true
   - Expected: gradient_end > gradient_start is true
   - Expected: gradient_body does not contain `unsigned int t_a`
   - Expected: gradient_body does not contain `unsigned int t_r`
   - Expected: gradient_body does not contain `unsigned int t_g`
   - Expected: gradient_body does not contain `unsigned int t_b`
   - Expected: gradient_body does not contain `unsigned int b_a`
   - Expected: gradient_body does not contain `unsigned int b_r`
   - Expected: gradient_body does not contain `unsigned int b_g`
   - Expected: gradient_body does not contain `unsigned int b_b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("kernel_draw_gradient_rect interpolates channels as signed int, not unsigned (descending-channel gradients must not wrap)")
# Regression: the channel locals used in the top/bottom interpolation
# MUST be signed. When a channel value decreases top-to-bottom (e.g.
# a light-to-dark gradient), `unsigned int` arithmetic wraps the
# negative delta to a huge positive value and integer division does
# not recover the correct signed result — corrupting every interior
# row on real ROCm hardware. The sibling CUDA PTX kernel
# (cuda_2d_gradient_ptx_source) explicitly converts to signed
# registers (`cvt.s32.u32`) before this arithmetic for exactly this
# reason; the HIP source here must match that behavior.
val source = _engine2d_hip_source()
val gradient_start = source.index_of("kernel_draw_gradient_rect")
expect(gradient_start >= 0).to_equal(true)
val gradient_end = source.index_of("kernel_blit_image", gradient_start)
expect(gradient_end > gradient_start).to_equal(true)
val gradient_body = source.slice(gradient_start, gradient_end)
expect(gradient_body).to_contain("int t_a =")
expect(gradient_body).to_contain("int t_r =")
expect(gradient_body).to_contain("int t_g =")
expect(gradient_body).to_contain("int t_b =")
expect(gradient_body).to_contain("int b_a =")
expect(gradient_body).to_contain("int b_r =")
expect(gradient_body).to_contain("int b_g =")
expect(gradient_body).to_contain("int b_b =")
expect(gradient_body.contains("unsigned int t_a")).to_equal(false)
expect(gradient_body.contains("unsigned int t_r")).to_equal(false)
expect(gradient_body.contains("unsigned int t_g")).to_equal(false)
expect(gradient_body.contains("unsigned int t_b")).to_equal(false)
expect(gradient_body.contains("unsigned int b_a")).to_equal(false)
expect(gradient_body.contains("unsigned int b_r")).to_equal(false)
expect(gradient_body.contains("unsigned int b_g")).to_equal(false)
expect(gradient_body.contains("unsigned int b_b")).to_equal(false)
```

</details>

#### rejects unsupported and current font batches before an uninitialized backend mutates

- rejects unsupported and current font batches before an uninitialized backend mutates
   - Expected: b.draw_font_batch(0, 0, _rocm_font_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION + 1)) equals `0`
   - Expected: b.draw_font_batch(0, 0, _rocm_font_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION)) equals `0`
   - Expected: b.initialized is false
   - Expected: b.hip_module equals `0`
   - Expected: b.host_buf.len() equals `0`
   - Expected: b.dirty is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unsupported and current font batches before an uninitialized backend mutates")
var b = RocmBackend.create()
expect(b.draw_font_batch(0, 0, _rocm_font_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION + 1))).to_equal(0)
expect(b.draw_font_batch(0, 0, _rocm_font_batch(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION))).to_equal(0)
expect(b.initialized).to_equal(false)
expect(b.hip_module).to_equal(0)
expect(b.host_buf.len()).to_equal(0)
expect(b.dirty).to_equal(false)
```

</details>

#### clear() on uninitialized backend does not crash

- clear() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("clear() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.clear(0xFF000000u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_rect() on uninitialized backend does not crash

- draw_rect() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_rect() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_rect(0, 0, 10, 10, 0xFFFFFFFFu32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_rect_filled() on uninitialized backend does not crash

- draw_rect_filled() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_rect_filled() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_rect_filled(0, 0, 10, 10, 0xFF0000FFu32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_line() on uninitialized backend does not crash

- draw_line() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_line() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_line(0, 0, 10, 10, 0xFF00FF00u32, 1)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_circle() on uninitialized backend does not crash

- draw_circle() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_circle() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_circle(5, 5, 4, 0xFFFF0000u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_circle_filled() on uninitialized backend does not crash

- draw_circle_filled() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_circle_filled() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_circle_filled(5, 5, 4, 0xFFFF0000u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_rounded_rect() on uninitialized backend does not crash

- draw_rounded_rect() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_rounded_rect() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_rounded_rect(0, 0, 20, 10, 3, 0xFF123456u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_triangle_filled() on uninitialized backend does not crash

- draw_triangle_filled() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_triangle_filled() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_triangle_filled(0, 0, 10, 0, 5, 10, 0xFF654321u32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_gradient_rect() on uninitialized backend does not crash

- draw_gradient_rect() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_gradient_rect() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_gradient_rect(0, 0, 10, 10, 0xFF000000u32, 0xFFFFFFFFu32)
expect(b.initialized).to_equal(false)
```

</details>

#### draw_image() on uninitialized backend does not crash

- draw_image() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_image() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_image(0, 0, 2, 2, [0xFFFFFFFFu32, 0xFF000000u32, 0xFF000000u32, 0xFFFFFFFFu32])
expect(b.initialized).to_equal(false)
```

</details>

#### draw_text() on uninitialized backend does not crash

- draw_text() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("draw_text() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.draw_text(0, 0, "hi", 0xFFFFFFFFu32, 12)
expect(b.initialized).to_equal(false)
```

</details>

### RocmBackend read_pixels and present guards (GPU-less)

#### read_pixels() on uninitialized backend returns empty array

- read_pixels() on uninitialized backend returns empty array
   - Expected: pixels.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("read_pixels() on uninitialized backend returns empty array")
var b = RocmBackend.create()
val pixels = b.read_pixels()
expect(pixels.len()).to_equal(0)
```

</details>

#### present() on uninitialized backend does not crash

- present() on uninitialized backend does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("present() on uninitialized backend does not crash")
var b = RocmBackend.create()
b.present()
expect(b.initialized).to_equal(false)
```

</details>

#### width() returns 0 before init

- width() returns 0 before init
   - Expected: b.width() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("width() returns 0 before init")
var b = RocmBackend.create()
expect(b.width()).to_equal(0)
```

</details>

#### height() returns 0 before init

- height() returns 0 before init
   - Expected: b.height() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("height() returns 0 before init")
var b = RocmBackend.create()
expect(b.height()).to_equal(0)
```

</details>

### RocmBackend probe error classification

#### probe_rocm feature_gate distinguishes hip-toolchain-missing from rocm-device-unavailable

- probe_rocm feature_gate distinguishes hip-toolchain-missing from rocm-device-unavailable
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_rocm feature_gate distinguishes hip-toolchain-missing from rocm-device-unavailable")
val probe = probe_rocm()
if probe.status != BackendStatus.Initialized:
    val gate = probe.feature_gate
    val known = (gate == "hip-toolchain-missing" or
                 gate == "rocm-init-failed" or
                 gate == "rocm-device-unavailable" or
                 gate == "rocm-kernel-gap")
    expect(known).to_equal(true)
```

</details>

#### probe_rocm sets has_compute false when no device

- probe_rocm sets has_compute false when no device
   - Expected: probe.has_compute is false
   - Expected: probe.has_graphics is false
   - Expected: probe.has_present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("probe_rocm sets has_compute false when no device")
val probe = probe_rocm()
if probe.feature_gate == "hip-toolchain-missing":
    expect(probe.has_compute).to_equal(false)
    expect(probe.has_graphics).to_equal(false)
    expect(probe.has_present).to_equal(false)
```

</details>

#### after init() last_probe feature_gate matches probe_rocm on this host

- after init() last_probe feature_gate matches probe_rocm on this host
   - Expected: b.last_probe.feature_gate equals `standalone.feature_gate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("after init() last_probe feature_gate matches probe_rocm on this host")
var b = RocmBackend.create()
b.init(64, 64)
val standalone = probe_rocm()
if standalone.status != BackendStatus.Initialized:
    expect(b.last_probe.feature_gate).to_equal(standalone.feature_gate)
```

</details>

#### shutdown() after failed init does not crash

- shutdown() after failed init does not crash
   - Expected: b.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shutdown() after failed init does not crash")
var b = RocmBackend.create()
b.init(64, 64)
b.shutdown()
expect(b.initialized).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RocmBackend init guards, RocmBackend draw-method init guards (GPU-less), RocmBackend read_pixels and present guards (GPU-less), RocmBackend probe error classification.
- RocmBackend init guards
- RocmBackend draw-method init guards (GPU-less)
- RocmBackend read_pixels and present guards (GPU-less)
- RocmBackend probe error classification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
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

- Canonical SPipe generation for source `ccd7e3d33580ee1b6013a7f2d273da33a394d892b251a85dc638a91348fed5dd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ccd7e3d33580ee1b6013a7f2d273da33a394d892b251a85dc638a91348fed5dd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ccd7e3d33580ee1b6013a7f2d273da33a394d892b251a85dc638a91348fed5dd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=20
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports device identity through both async ROCm facades' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds framebuffer multiplication before device or host allocation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_rocm_renderbackend_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create() yields initialized=false without AMD hardware' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
