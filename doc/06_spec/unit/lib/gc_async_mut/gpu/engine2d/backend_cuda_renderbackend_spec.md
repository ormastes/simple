# Backend Cuda Renderbackend Specification

> Tests covering CudaBackend RenderBackend facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Backend Cuda Renderbackend Specification

## Scenarios

### CudaBackend RenderBackend facade

#### fences the atlas cache with CUDA target and session identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fences the atlas cache with CUDA target and session identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fences the atlas cache with CUDA target and session identity")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
assert_contains(source, "font_atlas_composite_cache_identity(")
assert_contains(source, "font_render_batch_atlas_owner_identity(batch), \"cuda\", device_features")
assert_contains(source, "self.session.font_module_identity, dependency_identity")
```

</details>

#### declares explicit CUDA device and mirror authority

- declares explicit CUDA device and mirror authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares explicit CUDA device and mirror authority")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
assert_contains(source, "device_current: bool")
assert_contains(source, "mirror_current: bool")
assert_contains(source, "device_current: false,\n            mirror_current: true")
assert_contains(source, "me _ensure_device_current() -> bool:")
assert_contains(source, "me _ensure_mirror_current() -> bool:")
assert_contains(source, "me _begin_cpu_path() -> bool:")
assert_contains(source, "me _finish_cpu_path():")
assert_contains(source, "me _mark_device_mutation():")
```

</details>

#### keeps GPU success and CPU fallback authority transitions explicit

- keeps GPU success and CPU fallback authority transitions explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps GPU success and CPU fallback authority transitions explicit")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
assert_contains(source, "self._mark_device_mutation()")
assert_contains(source, "self._begin_cpu_path()")
assert_contains(source, "self._finish_cpu_path()")
assert_equal(source.contains("if rc == CUDA_SUCCESS:\n                self.mirror."), false)
expect(source).to_contain(
    "me _finish_cpu_path():\n" +
    "        self.cpu_fallback_used = true\n" +
    "        self.mirror_current = true\n" +
    "        self.device_current = false"
)
expect(source).to_contain(
    "me _mark_device_mutation():\n" +
    "        self.device_current = true\n" +
    "        self.mirror_current = false"
)
```

</details>

#### does not fall through to a stale mirror on readback

- does not fall through to a stale mirror on readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not fall through to a stale mirror on readback")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
assert_contains(source, "if self.mirror_current:")
assert_contains(source, "engine2d_readback([], \"readback_failed\")")
assert_equal(source.contains("engine2d_readback(self.mirror.read_pixels(), \"cpu_mirror\")"), false)
```

</details>

#### defers device upload after a failed clear kernel

- defers device upload after a failed clear kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defers device upload after a failed clear kernel")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(source).to_contain(
    "        if not self._begin_cpu_path():\n" +
    "            return\n" +
    "        self.mirror.clear(color)\n" +
    "        self._finish_cpu_path()\n" +
    "    me draw_rect("
)
expect(source).to_contain(
    "    me _ensure_device_current() -> bool:\n" +
    "        if self.device_current:\n" +
    "            return true\n" +
    "        self._copy_mirror_to_device()"
)
```

</details>

#### never promotes an emptied mirror during CUDA surface cleanup

- never promotes an emptied mirror during CUDA surface cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never promotes an emptied mirror during CUDA surface cleanup")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(source).to_contain(
    "me _cleanup_cuda_surface():\n" +
    "        self.cpu_fallback_used = false\n" +
    "        self.completion_unknown = false\n" +
    "        self.device_current = false\n" +
    "        self.mirror_current = false"
)
```

</details>

#### never labels CPU-rendered fallback pixels as device readback

- never labels CPU-rendered fallback pixels as device readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never labels CPU-rendered fallback pixels as device readback")
var backend = CudaBackend.create()
if backend.init(4, 4):
    backend.clear(0xff010203u32)
    val device_readback = backend.read_pixels_with_source()
    assert_equal(device_readback.source, "device_readback")
    expect(device_readback.backend_handle).to_be_greater_than(0)
    expect(device_readback.device_identity).to_be_greater_than(0)
    val stable_readback = backend.read_pixels_with_source()
    assert_equal(stable_readback.device_identity, device_readback.device_identity)
    backend.cpu_fallback_used = true
    val readback = backend.read_pixels_with_source()
    assert_equal(readback.source, "cpu_fallback")
    assert_equal(readback.backend_handle, 0)
    assert_equal(readback.device_identity, 0)
    assert_equal(readback.pixels.len(), 16)
else:
    assert_equal(backend.initialized, false)
backend.shutdown()
```

</details>

#### keeps CUDA completion failure sticky across readbacks

- keeps CUDA completion failure sticky across readbacks


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps CUDA completion failure sticky across readbacks")
var backend = CudaBackend.create()
backend.completion_unknown = true
val first = backend.read_pixels_with_source()
val second = backend.read_pixels_with_source()
assert_equal(first.source, "completion_unknown")
assert_equal(second.source, "completion_unknown")
assert_equal(first.pixels.len(), 0)
assert_equal(second.pixels.len(), 0)
```

</details>

#### quarantines accepted image work instead of freeing or overwriting it

- quarantines accepted image work instead of freeing or overwriting it


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("quarantines accepted image work instead of freeing or overwriting it")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(source).to_contain(
    "cuda_backend_free(host_pixels, image_bytes)\n" +
    "                    self._quarantine_completion_unknown()\n" +
    "                    return false"
)
expect(source).to_contain(
    "if self.completion_unknown:\n" +
    "            return\n" +
    "        if not self._begin_cpu_path():\n" +
    "            return\n" +
    "        self.mirror.draw_image("
)
expect(source).to_contain(
    "if self.completion_unknown or self.session.completion_unknown:\n" +
    "            self._quarantine_completion_unknown()\n" +
    "            return"
)
```

</details>

#### propagates CUDA font completion state to facade readback

- propagates CUDA font completion state to facade readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("propagates CUDA font completion state to facade readback")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(backend).to_contain(
    "if self.session.sync() != CUDA_SUCCESS:\n" +
    "                self._quarantine_completion_unknown()\n" +
    "                return submitted"
)
val engine = file_read("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
expect(engine).to_contain(
    "quad_index = cuda.draw_font_batch(x, y, batch)\n" +
    "                    self.cuda_backend = cuda\n" +
    "                    if self.selected_backend_name == \"cuda\":\n" +
    "                        self.backend = cuda"
)
expect(engine).to_contain(
    "elif self.selected_backend_name == \"cuda\":\n" +
    "            val cuda = self.cuda_backend.?\n" +
    "            val readback = cuda.read_pixels_with_source()\n" +
    "            self.cuda_backend = cuda\n" +
    "            self.backend = cuda"
)
```

</details>

#### reports the cuda backend name

- reports the cuda backend name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the cuda backend name")
val backend = CudaBackend.create()
assert_equal(backend.name(), "cuda")
```

</details>

#### returns a typed probe result

- returns a typed probe result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a typed probe result")
val probe = probe_cuda_2d()
val valid_status = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed
assert_equal(probe.requested_name, "cuda")
assert_equal(probe.api_name, "cuda")
assert_equal(probe.shader_format, "ptx")
assert_equal(valid_status, true)
```

</details>

#### exports probe_cuda with the same typed result

- exports probe_cuda with the same typed result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports probe_cuda with the same typed result")
val probe = probe_cuda()
val valid_status = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed
assert_equal(probe.requested_name, "cuda")
assert_equal(probe.api_name, "cuda")
assert_equal(probe.shader_format, "ptx")
assert_equal(valid_status, true)
```

</details>

#### exports generated fill and image blend entries in CUDA PTX module source

- exports generated fill and image blend entries in CUDA PTX module source


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports generated fill and image blend entries in CUDA PTX module source")
val source = cuda_2d_ptx_source()

assert_contains(source, "simple_2d_fill_u32")
assert_contains(source, "kernel_draw_image_nonzero")
assert_contains(source, "kernel_draw_image_blend")
assert_contains(source, "param_width")
assert_contains(source, "param_height")
```

</details>

#### routes both CUDA image blend interfaces through the native kernel

- routes both CUDA image blend interfaces through the native kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes both CUDA image blend interfaces through the native kernel")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
val extended = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda_ext.spl")
assert_contains(backend, "self._draw_image_kernel(\"kernel_draw_image_blend\"")
assert_contains(backend, "self._draw_image_blend_or_fallback(x, y, w, h, pixels)")
assert_contains(extended, "self._draw_image_blend_or_fallback(x, y, w, h, pixels)")
```

</details>

#### keeps the generated font entry out of the default CUDA module

- keeps the generated font entry out of the default CUDA module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the generated font entry out of the default CUDA module")
val source = cuda_2d_ptx_source()
assert_equal(source.contains(FONT_ATLAS_COMPOSITE_ENTRY), false)
```

</details>

#### pins an installed generated font companion by exact PTX identity

- pins an installed generated font companion by exact PTX identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pins an installed generated font companion by exact PTX identity")
val ptx = ".version 8.0\n.visible .entry simple_font_atlas_composite_v1_u32() { ret; }\n"
var session = CudaSession.create()
assert_equal(session.install_font_module(""), false)
assert_equal(session.install_font_module(".version 8.0\n"), false)
assert_equal(session.install_font_module(".version 8.0\n.entry simple_font_atlas_composite_v1_u32_suffix() { ret; }\n"), false)
session.module_cache = 9
assert_equal(session.launch_font_kernel_args(1, 1, 1, 1, 1, 1, 1), 1)
session.font_module_cache = 17
session.font_module_identity = "generated-ptx:" + sha256_text(ptx)
assert_equal(session.install_font_module(ptx), true)
assert_equal(session.install_font_module(ptx + " "), false)

var backend = CudaBackend.create()
backend.initialized = true
backend.font_atlas_generation = 9
backend.session = session
assert_equal(backend.install_font_atlas_ptx(ptx), true)
assert_equal(backend.font_atlas_generation, 9)
assert_equal(backend.install_font_atlas_ptx(ptx + " "), false)
assert_equal(backend.font_atlas_generation, 9)
```

</details>

#### rejects inconsistent caller-provided font artifacts without mutation

- rejects inconsistent caller-provided font artifacts without mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects inconsistent caller-provided font artifacts without mutation")
val ptx = ".version 8.0\n.visible .entry simple_font_atlas_composite_v1_u32() { ret; }\n"
val artifact_sha256 = sha256_text(ptx)
var session = CudaSession.create()
session.font_module_cache = 17
session.font_module_identity = "generated-ptx:" + artifact_sha256
var cuda = CudaBackend.create()
cuda.initialized = true
cuda.session = session
var engine = Engine2D.create_with_backend(1, 1, "software")
engine.cuda_backend = cuda

val wrong_entry = ".version 8.0\n.visible .entry wrong_font_entry() { ret; }\n"
assert_equal(engine.install_cuda_font_artifact("", sha256_text(""), FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION), false)
assert_equal(engine.install_cuda_font_artifact(ptx, "0000000000000000000000000000000000000000000000000000000000000000", FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION), false)
assert_equal(engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION + 1, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION), false)
assert_equal(engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION - 1), false)
assert_equal(engine.install_cuda_font_artifact(wrong_entry, sha256_text(wrong_entry), FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION), false)
assert_equal(engine.cuda_backend.?.session.font_module_cache, 17)
assert_equal(engine.cuda_backend.?.session.font_module_identity, "generated-ptx:" + artifact_sha256)
assert_equal(engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION), true)
engine.cuda_backend = nil
engine.shutdown()
```

</details>

#### rejects the stale tracked CUDA font semantics without a device load

- rejects the stale tracked CUDA font semantics without a device load


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the stale tracked CUDA font semantics without a device load")
val ptx = cuda_font_atlas_composite_ptx()
assert_equal(FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256, sha256_text(ptx))
assert_equal(FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION)
assert_not_equal(FONT_ATLAS_COMPOSITE_CUDA_SEMANTICS_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)
assert_equal(cuda_font_atlas_composite_ptx_trusted(ptx), false)
assert_equal(cuda_font_atlas_composite_ptx_trusted(ptx + " "), false)

var session = CudaSession.create()
session.font_module_cache = 17
session.font_module_identity = "generated-ptx:" + FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256
var cuda = CudaBackend.create()
cuda.initialized = true
cuda.session = session
var engine = Engine2D.create_with_backend(1, 1, "software")
engine.cuda_backend = cuda
assert_equal(engine.install_pinned_cuda_font_artifact(), false)
engine.cuda_backend = nil
engine.shutdown()
```

</details>

#### fails closed for invalid font batches and invalidates atlas generations

- fails closed for invalid font batches and invalidates atlas generations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed for invalid font batches and invalidates atlas generations")
var backend = CudaBackend.create()
val invalid = FontRenderBatch(program_version: 1, font_identity: "test-font", face_generation: 1, valid: false, atlas_width: 0, atlas_height: 0, atlas_pixels: [], quads: [], atlas_generation: 0, dirty_rects: [])

assert_equal(backend.draw_font_batch(0, 0, invalid), 0)
backend.font_atlas_generation = 7
backend.font_atlas_owner_identity = "stale-owner"
backend.invalidate_font_atlas()
assert_equal(backend.font_atlas_generation, -1)
assert_equal(backend.font_atlas_owner_identity, "")
```

</details>

#### rejects unsupported font programs before CUDA atlas mutation

- rejects unsupported font programs before CUDA atlas mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsupported font programs before CUDA atlas mutation")
var backend = CudaBackend.create()
backend.font_atlas_generation = 7
backend.font_atlas_owner_identity = "stable-owner"
for version in [0, -1, 2]:
    val batch = FontRenderBatch(program_version: version, font_identity: "test-font", face_generation: 1, valid: true, atlas_width: 1, atlas_height: 1,
        atlas_pixels: [1u32], quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0, width: 1, height: 1, atlas_x: 0, atlas_y: 0, color: 1u32)], atlas_generation: 8, dirty_rects: [])
    assert_equal(backend.draw_font_batch(0, 0, batch), 0)
    assert_equal(backend.font_atlas_generation, 7)
    assert_equal(backend.font_atlas_owner_identity, "stable-owner")
```

</details>

#### requires the generated companion before CUDA font dispatch

- requires the generated companion before CUDA font dispatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the generated companion before CUDA font dispatch")
var backend = CudaBackend.create()
val ok = backend.init(4, 4)
if ok:
    val batch = FontRenderBatch(
        program_version: 1,
        font_identity: "test-font", face_generation: 1,
        valid: true, atlas_width: 1, atlas_height: 1,
        atlas_pixels: [0x80000000u32],
        quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 1, dst_y: 1, width: 1, height: 1, atlas_x: 0, atlas_y: 0, color: 0x80ff0000u32)],
        atlas_generation: 1, dirty_rects: []
    )
    assert_equal(backend.session.font_module_cache, 0)
    assert_equal(backend.draw_font_batch(0, 0, batch), 0)
    assert_equal(backend.font_atlas_generation, -1)
    assert_equal(backend.font_atlas_owner_identity, "")
else:
    assert_equal(backend.initialized, false)
backend.shutdown()
```

</details>

#### does not claim initialized when init fails

- does not claim initialized when init fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not claim initialized when init fails")
var backend = CudaBackend.create()
val ok = backend.init(4, 4)
if ok:
    assert_equal(backend.width(), 4)
    assert_equal(backend.height(), 4)
    backend.shutdown()
else:
    assert_equal(backend.initialized, false)
    assert_equal(backend.owns_session, false)
```

</details>

#### routes draw_text_bg through the shared text image path without CUDA hardware

- routes draw_text_bg through the shared text image path without CUDA hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes draw_text_bg through the shared text image path without CUDA hardware")
var backend = CudaBackend.create()
assert_equal(backend.mirror.init(4, 4), true)

backend.draw_text_bg(0, 0, "I", 0xff111111u32, 0xff222222u32, 7)
val text_bg = backend.read_pixels()
val expected = text_render_to_buf("I", 0xff111111u32, 0xff222222u32, 7)

assert_equal(text_bg[0], expected[0])
assert_equal(text_bg[1], expected[1])
assert_equal(text_bg[2], expected[2])
assert_equal(text_bg[3], expected[3])
backend.shutdown()
```

</details>

#### routes foreground draw_text through transparent text image semantics without CUDA hardware

- routes foreground draw_text through transparent text image semantics without CUDA hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes foreground draw_text through transparent text image semantics without CUDA hardware")
var backend = CudaBackend.create()
val bg = 0xff333333u32
assert_equal(backend.mirror.init(4, 4), true)
backend.mirror.clear(bg)

backend.draw_text(0, 0, "I", 0xff111111u32, 7)
val text_pixels = backend.read_pixels()
val expected = text_render_to_buf("I", 0xff111111u32, 0u32, 7)
var fg_count = 0
var bg_count = 0
var transparent_count = 0
var idx = 0
while idx < 16:
    if text_pixels[idx] == 0xff111111u32:
        fg_count = fg_count + 1
    if text_pixels[idx] == bg:
        bg_count = bg_count + 1
    if expected[idx] == 0u32:
        transparent_count = transparent_count + 1
    idx = idx + 1

assert_equal(fg_count > 0, true)
assert_equal(bg_count > 0, true)
assert_equal(transparent_count > 0, true)
backend.shutdown()
```

</details>

#### rejects an invalid shared CUDA session with typed context diagnostics

- rejects an invalid shared CUDA session with typed context diagnostics


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an invalid shared CUDA session with typed context diagnostics")
var backend = CudaBackend.create()
var session = CudaSession.create()
val ok = backend.init_with_session(4, 4, session)
assert_equal(ok, false)
assert_equal(backend.initialized, false)
assert_equal(backend.owns_session, false)
assert_equal(backend.last_probe.requested_name, "cuda")
assert_equal(backend.last_probe.api_name, "cuda")
assert_equal(backend.last_probe.feature_gate, "cuda_context")
assert_equal(backend.last_probe.status, BackendStatus.Failed)
```

</details>

#### rejects active CUDA session replacement without mutating atlas ownership

- rejects active CUDA session replacement without mutating atlas ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects active CUDA session replacement without mutating atlas ownership")
var backend = CudaBackend.create()
backend.initialized = true
backend.owns_session = true
backend.d_font_atlas = 77
backend.font_atlas_generation = 9
backend.font_atlas_owner_identity = "old"
var incoming = CudaSession.create()
incoming.is_initialized = true
incoming.ctx = 1
incoming.ref_count = 2
assert_equal(backend.init_with_session(4, 4, incoming), false)
assert_equal(incoming.ref_count, 2)
assert_equal(backend.d_font_atlas, 77)
assert_equal(backend.font_atlas_generation, 9)
assert_equal(backend.font_atlas_owner_identity, "old")
assert_equal(backend.owns_session, true)
var invalid = CudaSession.create()
assert_equal(backend.init_with_session(0, 4, invalid), false)
assert_equal(backend.initialized, true)
assert_equal(backend.owns_session, true)
assert_equal(backend.d_font_atlas, 77)
assert_equal(invalid.ref_count, 0)
```

</details>

#### reports CUDA 2D kernel readiness or the real kernel gap

- reports CUDA 2D kernel readiness or the real kernel gap


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports CUDA 2D kernel readiness or the real kernel gap")
val probe = probe_cuda_2d()
if probe.status == BackendStatus.Initialized:
    assert_equal(probe.is_usable(), true)
    assert_equal(probe.has_compute, true)
    assert_equal(probe.has_graphics, true)
    assert_equal(probe.has_present, true)
else if probe.feature_gate == "cuda_2d_render":
    assert_equal(probe.status, BackendStatus.Failed)
    assert_equal(probe.is_usable(), false)
    assert_equal(probe.has_compute, true)
    assert_equal(probe.has_graphics, false)
    assert_equal(probe.has_present, false)
    assert_contains(probe.fallback_reason, "simple_2d_fill_u32")
    assert_contains(probe.fallback_reason, "kernel_clear")
    assert_contains(probe.fallback_reason, "kernel_draw_rect_filled")
    assert_contains(probe.fallback_reason, "kernel_draw_rect_outline")
    assert_contains(probe.fallback_reason, "kernel_draw_image")
    assert_contains(probe.fallback_reason, "kernel_draw_gradient_rect")
    assert_contains(probe.fallback_reason, "kernel_draw_line")
else:
    # Neither recognised shape. Both branches above are claims about the
    # probe OBJECT (self-consistency), not predictions about a later
    # create, so they stay hard assertions — but a probe that matches
    # neither must not slip through as a silent pass.
    assert_equal(probe.is_usable(), probe.status == BackendStatus.Initialized)
    print "[cuda-2d] cuda-2d-readiness: NEITHER SHAPE MATCHED — status is not Initialized and feature_gate is '{probe.feature_gate}', not 'cuda_2d_render'; this example proves NOTHING about the 2D kernel gap"
```

</details>

#### does not mark CUDA usable when the PTX self-test fails

- does not mark CUDA usable when the PTX self-test fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not mark CUDA usable when the PTX self-test fails")
val probe = probe_cuda_2d()
if probe.feature_gate == "cuda_2d_render_self_test":
    assert_equal(probe.status, BackendStatus.Failed)
    assert_equal(probe.is_usable(), false)
    assert_equal(probe.has_compute, true)
    assert_equal(probe.has_graphics, false)
    assert_equal(probe.has_present, false)
    assert_contains(probe.fallback_reason, "self-test")
else:
    # The self-test gate was not the one that fired, so the body above
    # never ran. Disclose it instead of reporting a silent pass.
    assert_equal(probe.is_usable(), probe.status == BackendStatus.Initialized)
    print "[cuda-2d] cuda-2d-self-test: SELF-TEST GATE NOT EXERCISED — feature_gate is '{probe.feature_gate}', not 'cuda_2d_render_self_test'; this example proves NOTHING about the PTX self-test path"
```

</details>

#### strict Engine2D cuda creation returns typed cuda failure instead of fallback

- strict Engine2D cuda creation returns typed cuda failure instead of fallback


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strict Engine2D cuda creation returns typed cuda failure instead of fallback")
# PROBE-THEN-CREATE TOCTOU
# (doc/08_tracking/bug/gpu_probe_then_create_toctou_2026-08-04.md)
# This example used to read probe_cuda_2d(), gate on
# `probe.status != Initialized`, and only THEN run a second, independent
# Engine2D.create_with_backend_strict — asserting `result.is_ok()` MUST
# be FALSE purely because the probe had predicted failure. Nothing is
# cached between the two, so that was a prediction, not a fact, and it
# broke in both directions: a create that succeeds where the probe
# predicted failure is a FALSE RED, and a probe that reports Initialized
# skipped the whole body for a VACUOUS GREEN. On this very host
# probe_cuda() reports unusable while create_with_backend_strict("cuda")
# succeeds with a genuine device_readback, so the false red is live.
#
# The create is now attempted UNCONDITIONALLY and every assertion reads
# the CREATE's own outcome. The probe is only DISCLOSED.
val probe = probe_cuda_2d()
val probe_ready = probe.status == BackendStatus.Initialized
val result = Engine2D.create_with_backend_strict(4, 4, "cuda")
val created = result.is_ok()
if probe_ready != created:
    print "[toctou] cuda-strict-typed-failure: probe predicted initialized={probe_ready} but the independent create returned ok={created} — the prediction did not survive the gap; asserting on the CREATE, not the probe"
if not created:
    # A strict cuda create that fails must fail STRUCTURALLY: typed
    # terminal status, the cuda name preserved on every field, and never
    # a silent cpu/software substitute or a Fallback demotion.
    val diag = result.unwrap_err()
    assert_equal(diag.requested_name, "cuda")
    assert_equal(diag.selected_name, "cuda")
    assert_equal(diag.backend_name, "cuda")
    assert_equal(diag.status == BackendStatus.Unavailable or diag.status == BackendStatus.Failed, true)
    expect(diag.status).to_not_equal(BackendStatus.Fallback)
else:
    # The strictness claim still holds on the success path, so this
    # branch is not a silent skip either.
    var engine = result.unwrap()
    assert_equal(engine.backend_name(), "cuda")
    engine.shutdown()
    print "[cuda-2d] cuda-strict-typed-failure: FAILURE PATH NOT EXERCISED — the strict cuda create succeeded, so this example proves NOTHING about the typed-failure path"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CudaBackend RenderBackend facade.
- CudaBackend RenderBackend facade

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

- Canonical SPipe generation for source `e533b59c6967d08cbbcf57b44c23d14f4c40d1dcf3a476fc80ab62a1aaad376d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e533b59c6967d08cbbcf57b44c23d14f4c40d1dcf3a476fc80ab62a1aaad376d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e533b59c6967d08cbbcf57b44c23d14f4c40d1dcf3a476fc80ab62a1aaad376d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.md (current)
findings: 6 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fences the atlas cache with CUDA target and session identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares explicit CUDA device and mirror authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps GPU success and CPU fallback authority transitions explicit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
