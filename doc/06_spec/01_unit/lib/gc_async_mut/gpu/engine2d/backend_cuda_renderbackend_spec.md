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
# @req REQ-SSPEC-LIB
step("fences the atlas cache with CUDA target and session identity")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(source).to_contain("font_atlas_composite_cache_identity(")
expect(source).to_contain("font_render_batch_atlas_owner_identity(batch), \"cuda\", device_features")
expect(source).to_contain("self.session.font_module_identity, dependency_identity")
```

</details>

#### declares explicit CUDA device and mirror authority

- declares explicit CUDA device and mirror authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("declares explicit CUDA device and mirror authority")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(source).to_contain("device_current: bool")
expect(source).to_contain("mirror_current: bool")
expect(source).to_contain("device_current: false,\n            mirror_current: true")
expect(source).to_contain("me _ensure_device_current() -> bool:")
expect(source).to_contain("me _ensure_mirror_current() -> bool:")
expect(source).to_contain("me _begin_cpu_path() -> bool:")
expect(source).to_contain("me _finish_cpu_path():")
expect(source).to_contain("me _mark_device_mutation():")
```

</details>

#### keeps GPU success and CPU fallback authority transitions explicit

- keeps GPU success and CPU fallback authority transitions explicit
   - Expected: source does not contain `if rc == CUDA_SUCCESS:\n                self.mirror.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps GPU success and CPU fallback authority transitions explicit")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(source).to_contain("self._mark_device_mutation()")
expect(source).to_contain("self._begin_cpu_path()")
expect(source).to_contain("self._finish_cpu_path()")
expect(source.contains("if rc == CUDA_SUCCESS:\n                self.mirror.")).to_equal(false)
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
   - Expected: source does not contain `engine2d_readback(self.mirror.read_pixels(), "cpu_mirror")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not fall through to a stale mirror on readback")
val source = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
expect(source).to_contain("if self.mirror_current:")
expect(source).to_contain("engine2d_readback([], \"readback_failed\")")
expect(source.contains("engine2d_readback(self.mirror.read_pixels(), \"cpu_mirror\")")).to_equal(false)
```

</details>

#### defers device upload after a failed clear kernel

- defers device upload after a failed clear kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
   - Expected: device_readback.source equals `device_readback`
   - Expected: stable_readback.device_identity equals `device_readback.device_identity`
   - Expected: readback.source equals `cpu_fallback`
   - Expected: readback.backend_handle equals `0`
   - Expected: readback.device_identity equals `0`
   - Expected: readback.pixels.len() equals `16`
   - Expected: backend.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never labels CPU-rendered fallback pixels as device readback")
var backend = CudaBackend.create()
if backend.init(4, 4):
    backend.clear(0xff010203u32)
    val device_readback = backend.read_pixels_with_source()
    expect(device_readback.source).to_equal("device_readback")
    expect(device_readback.backend_handle).to_be_greater_than(0)
    expect(device_readback.device_identity).to_be_greater_than(0)
    val stable_readback = backend.read_pixels_with_source()
    expect(stable_readback.device_identity).to_equal(device_readback.device_identity)
    backend.cpu_fallback_used = true
    val readback = backend.read_pixels_with_source()
    expect(readback.source).to_equal("cpu_fallback")
    expect(readback.backend_handle).to_equal(0)
    expect(readback.device_identity).to_equal(0)
    expect(readback.pixels.len()).to_equal(16)
else:
    expect(backend.initialized).to_equal(false)
backend.shutdown()
```

</details>

#### keeps CUDA completion failure sticky across readbacks

- keeps CUDA completion failure sticky across readbacks
   - Expected: first.source equals `completion_unknown`
   - Expected: second.source equals `completion_unknown`
   - Expected: first.pixels.len() equals `0`
   - Expected: second.pixels.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps CUDA completion failure sticky across readbacks")
var backend = CudaBackend.create()
backend.completion_unknown = true
val first = backend.read_pixels_with_source()
val second = backend.read_pixels_with_source()
expect(first.source).to_equal("completion_unknown")
expect(second.source).to_equal("completion_unknown")
expect(first.pixels.len()).to_equal(0)
expect(second.pixels.len()).to_equal(0)
```

</details>

#### quarantines accepted image work instead of freeing or overwriting it

- quarantines accepted image work instead of freeing or overwriting it


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
# @req REQ-SSPEC-LIB
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
   - Expected: backend.name() equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the cuda backend name")
val backend = CudaBackend.create()
expect(backend.name()).to_equal("cuda")
```

</details>

#### returns a typed probe result

- returns a typed probe result
   - Expected: probe.requested_name equals `cuda`
   - Expected: probe.api_name equals `cuda`
   - Expected: probe.shader_format equals `ptx`
   - Expected: valid_status is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a typed probe result")
val probe = probe_cuda_2d()
val valid_status = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed
expect(probe.requested_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
expect(valid_status).to_equal(true)
```

</details>

#### exports probe_cuda with the same typed result

- exports probe_cuda with the same typed result
   - Expected: probe.requested_name equals `cuda`
   - Expected: probe.api_name equals `cuda`
   - Expected: probe.shader_format equals `ptx`
   - Expected: valid_status is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports probe_cuda with the same typed result")
val probe = probe_cuda()
val valid_status = probe.status == BackendStatus.Initialized or probe.status == BackendStatus.Unavailable or probe.status == BackendStatus.Failed
expect(probe.requested_name).to_equal("cuda")
expect(probe.api_name).to_equal("cuda")
expect(probe.shader_format).to_equal("ptx")
expect(valid_status).to_equal(true)
```

</details>

#### exports generated fill and image blend entries in CUDA PTX module source

- exports generated fill and image blend entries in CUDA PTX module source


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports generated fill and image blend entries in CUDA PTX module source")
val source = cuda_2d_ptx_source()

expect(source).to_contain("simple_2d_fill_u32")
expect(source).to_contain("kernel_draw_image_nonzero")
expect(source).to_contain("kernel_draw_image_blend")
expect(source).to_contain("param_width")
expect(source).to_contain("param_height")
```

</details>

#### routes both CUDA image blend interfaces through the native kernel

- routes both CUDA image blend interfaces through the native kernel


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes both CUDA image blend interfaces through the native kernel")
val backend = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl")
val extended = file_read("src/lib/gc_async_mut/gpu/engine2d/backend_cuda_ext.spl")
expect(backend).to_contain("self._draw_image_kernel(\"kernel_draw_image_blend\"")
expect(backend).to_contain("self._draw_image_blend_or_fallback(x, y, w, h, pixels)")
expect(extended).to_contain("self._draw_image_blend_or_fallback(x, y, w, h, pixels)")
```

</details>

#### keeps the generated font entry out of the default CUDA module

- keeps the generated font entry out of the default CUDA module
   - Expected: source does not contain `FONT_ATLAS_COMPOSITE_ENTRY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the generated font entry out of the default CUDA module")
val source = cuda_2d_ptx_source()
expect(source.contains(FONT_ATLAS_COMPOSITE_ENTRY)).to_equal(false)
```

</details>

#### pins an installed generated font companion by exact PTX identity

- pins an installed generated font companion by exact PTX identity
   - Expected: session.install_font_module("") is false
   - Expected: session.install_font_module(".version 8.0\n") is false
   - Expected: session.install_font_module(".version 8.0\n.entry simple_font_atlas_composite_v1_u32_suffix() { ret; }\n") is false
   - Expected: session.launch_font_kernel_args(1, 1, 1, 1, 1, 1, 1) equals `1`
   - Expected: session.install_font_module(ptx) is true
   - Expected: session.install_font_module(ptx + " ") is false
   - Expected: backend.install_font_atlas_ptx(ptx) is true
   - Expected: backend.font_atlas_generation equals `9`
   - Expected: backend.install_font_atlas_ptx(ptx + " ") is false
   - Expected: backend.font_atlas_generation equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pins an installed generated font companion by exact PTX identity")
val ptx = ".version 8.0\n.visible .entry simple_font_atlas_composite_v1_u32() { ret; }\n"
var session = CudaSession.create()
expect(session.install_font_module("")).to_equal(false)
expect(session.install_font_module(".version 8.0\n")).to_equal(false)
expect(session.install_font_module(".version 8.0\n.entry simple_font_atlas_composite_v1_u32_suffix() { ret; }\n")).to_equal(false)
session.module_cache = 9
expect(session.launch_font_kernel_args(1, 1, 1, 1, 1, 1, 1)).to_equal(1)
session.font_module_cache = 17
session.font_module_identity = "generated-ptx:" + sha256_text(ptx)
expect(session.install_font_module(ptx)).to_equal(true)
expect(session.install_font_module(ptx + " ")).to_equal(false)

var backend = CudaBackend.create()
backend.initialized = true
backend.font_atlas_generation = 9
backend.session = session
expect(backend.install_font_atlas_ptx(ptx)).to_equal(true)
expect(backend.font_atlas_generation).to_equal(9)
expect(backend.install_font_atlas_ptx(ptx + " ")).to_equal(false)
expect(backend.font_atlas_generation).to_equal(9)
```

</details>

#### rejects inconsistent caller-provided font artifacts without mutation

- rejects inconsistent caller-provided font artifacts without mutation
   - Expected: engine.install_cuda_font_artifact("", sha256_text(""), FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION) is false
   - Expected: engine.install_cuda_font_artifact(ptx, "0000000000000000000000000000000000000000000000000000000000000000", FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION) is false
   - Expected: engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION + 1, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION) is false
   - Expected: engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION - 1) is false
   - Expected: engine.install_cuda_font_artifact(wrong_entry, sha256_text(wrong_entry), FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION) is false
   - Expected: engine.cuda_backend.?.session.font_module_cache equals `17`
   - Expected: engine.cuda_backend.?.session.font_module_identity equals `"generated-ptx:" + artifact_sha256`
   - Expected: engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
expect(engine.install_cuda_font_artifact("", sha256_text(""), FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)).to_equal(false)
expect(engine.install_cuda_font_artifact(ptx, "0000000000000000000000000000000000000000000000000000000000000000", FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)).to_equal(false)
expect(engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION + 1, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)).to_equal(false)
expect(engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION - 1)).to_equal(false)
expect(engine.install_cuda_font_artifact(wrong_entry, sha256_text(wrong_entry), FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)).to_equal(false)
expect(engine.cuda_backend.?.session.font_module_cache).to_equal(17)
expect(engine.cuda_backend.?.session.font_module_identity).to_equal("generated-ptx:" + artifact_sha256)
expect(engine.install_cuda_font_artifact(ptx, artifact_sha256, FONT_ATLAS_COMPOSITE_PROGRAM_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)).to_equal(true)
engine.cuda_backend = nil
engine.shutdown()
```

</details>

#### rejects the stale tracked CUDA font semantics without a device load

- rejects the stale tracked CUDA font semantics without a device load
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256 equals `sha256_text(ptx)`
   - Expected: FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION equals `FONT_ATLAS_COMPOSITE_PROGRAM_VERSION`
   - Expected: cuda_font_atlas_composite_ptx_trusted(ptx) is false
   - Expected: cuda_font_atlas_composite_ptx_trusted(ptx + " ") is false
   - Expected: engine.install_pinned_cuda_font_artifact() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects the stale tracked CUDA font semantics without a device load")
val ptx = cuda_font_atlas_composite_ptx()
expect(FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256).to_equal(sha256_text(ptx))
expect(FONT_ATLAS_COMPOSITE_CUDA_PROGRAM_VERSION).to_equal(FONT_ATLAS_COMPOSITE_PROGRAM_VERSION)
assert_not_equal(FONT_ATLAS_COMPOSITE_CUDA_SEMANTICS_VERSION, FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION)
expect(cuda_font_atlas_composite_ptx_trusted(ptx)).to_equal(false)
expect(cuda_font_atlas_composite_ptx_trusted(ptx + " ")).to_equal(false)

var session = CudaSession.create()
session.font_module_cache = 17
session.font_module_identity = "generated-ptx:" + FONT_ATLAS_COMPOSITE_CUDA_PTX_SHA256
var cuda = CudaBackend.create()
cuda.initialized = true
cuda.session = session
var engine = Engine2D.create_with_backend(1, 1, "software")
engine.cuda_backend = cuda
expect(engine.install_pinned_cuda_font_artifact()).to_equal(false)
engine.cuda_backend = nil
engine.shutdown()
```

</details>

#### fails closed for invalid font batches and invalidates atlas generations

- fails closed for invalid font batches and invalidates atlas generations
   - Expected: backend.draw_font_batch(0, 0, invalid) equals `0`
   - Expected: backend.font_atlas_generation equals `-1`
   - Expected: backend.font_atlas_owner_identity equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed for invalid font batches and invalidates atlas generations")
var backend = CudaBackend.create()
val invalid = FontRenderBatch(program_version: 1, font_identity: "test-font", face_generation: 1, valid: false, atlas_width: 0, atlas_height: 0, atlas_pixels: [], quads: [], atlas_generation: 0, dirty_rects: [])

expect(backend.draw_font_batch(0, 0, invalid)).to_equal(0)
backend.font_atlas_generation = 7
backend.font_atlas_owner_identity = "stale-owner"
backend.invalidate_font_atlas()
expect(backend.font_atlas_generation).to_equal(-1)
expect(backend.font_atlas_owner_identity).to_equal("")
```

</details>

#### rejects unsupported font programs before CUDA atlas mutation

- rejects unsupported font programs before CUDA atlas mutation
   - Expected: backend.draw_font_batch(0, 0, batch) equals `0`
   - Expected: backend.font_atlas_generation equals `7`
   - Expected: backend.font_atlas_owner_identity equals `stable-owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects unsupported font programs before CUDA atlas mutation")
var backend = CudaBackend.create()
backend.font_atlas_generation = 7
backend.font_atlas_owner_identity = "stable-owner"
for version in [0, -1, 2]:
    val batch = FontRenderBatch(program_version: version, font_identity: "test-font", face_generation: 1, valid: true, atlas_width: 1, atlas_height: 1,
        atlas_pixels: [1u32], quads: [FontRenderQuad(codepoint: 65, byte_offset: 0, dst_x: 0, dst_y: 0, width: 1, height: 1, atlas_x: 0, atlas_y: 0, color: 1u32)], atlas_generation: 8, dirty_rects: [])
    expect(backend.draw_font_batch(0, 0, batch)).to_equal(0)
    expect(backend.font_atlas_generation).to_equal(7)
    expect(backend.font_atlas_owner_identity).to_equal("stable-owner")
```

</details>

#### requires the generated companion before CUDA font dispatch

- requires the generated companion before CUDA font dispatch
   - Expected: backend.session.font_module_cache equals `0`
   - Expected: backend.draw_font_batch(0, 0, batch) equals `0`
   - Expected: backend.font_atlas_generation equals `-1`
   - Expected: backend.font_atlas_owner_identity equals ``
   - Expected: backend.initialized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
    expect(backend.session.font_module_cache).to_equal(0)
    expect(backend.draw_font_batch(0, 0, batch)).to_equal(0)
    expect(backend.font_atlas_generation).to_equal(-1)
    expect(backend.font_atlas_owner_identity).to_equal("")
else:
    expect(backend.initialized).to_equal(false)
backend.shutdown()
```

</details>

#### does not claim initialized when init fails

- does not claim initialized when init fails
   - Expected: backend.width() equals `4`
   - Expected: backend.height() equals `4`
   - Expected: backend.initialized is false
   - Expected: backend.owns_session is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not claim initialized when init fails")
var backend = CudaBackend.create()
val ok = backend.init(4, 4)
if ok:
    expect(backend.width()).to_equal(4)
    expect(backend.height()).to_equal(4)
    backend.shutdown()
else:
    expect(backend.initialized).to_equal(false)
    expect(backend.owns_session).to_equal(false)
```

</details>

#### routes draw_text_bg through the shared text image path without CUDA hardware

- routes draw_text_bg through the shared text image path without CUDA hardware
   - Expected: backend.mirror.init(4, 4) is true
   - Expected: text_bg[0] equals `expected[0]`
   - Expected: text_bg[1] equals `expected[1]`
   - Expected: text_bg[2] equals `expected[2]`
   - Expected: text_bg[3] equals `expected[3]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes draw_text_bg through the shared text image path without CUDA hardware")
var backend = CudaBackend.create()
expect(backend.mirror.init(4, 4)).to_equal(true)

backend.draw_text_bg(0, 0, "I", 0xff111111u32, 0xff222222u32, 7)
val text_bg = backend.read_pixels()
val expected = text_render_to_buf("I", 0xff111111u32, 0xff222222u32, 7)

expect(text_bg[0]).to_equal(expected[0])
expect(text_bg[1]).to_equal(expected[1])
expect(text_bg[2]).to_equal(expected[2])
expect(text_bg[3]).to_equal(expected[3])
backend.shutdown()
```

</details>

#### routes foreground draw_text through transparent text image semantics without CUDA hardware

- routes foreground draw_text through transparent text image semantics without CUDA hardware
   - Expected: backend.mirror.init(4, 4) is true
   - Expected: fg_count > 0 is true
   - Expected: bg_count > 0 is true
   - Expected: transparent_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("routes foreground draw_text through transparent text image semantics without CUDA hardware")
var backend = CudaBackend.create()
val bg = 0xff333333u32
expect(backend.mirror.init(4, 4)).to_equal(true)
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

expect(fg_count > 0).to_equal(true)
expect(bg_count > 0).to_equal(true)
expect(transparent_count > 0).to_equal(true)
backend.shutdown()
```

</details>

#### rejects an invalid shared CUDA session with typed context diagnostics

- rejects an invalid shared CUDA session with typed context diagnostics
   - Expected: ok is false
   - Expected: backend.initialized is false
   - Expected: backend.owns_session is false
   - Expected: backend.last_probe.requested_name equals `cuda`
   - Expected: backend.last_probe.api_name equals `cuda`
   - Expected: backend.last_probe.feature_gate equals `cuda_context`
   - Expected: backend.last_probe.status equals `BackendStatus.Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an invalid shared CUDA session with typed context diagnostics")
var backend = CudaBackend.create()
var session = CudaSession.create()
val ok = backend.init_with_session(4, 4, session)
expect(ok).to_equal(false)
expect(backend.initialized).to_equal(false)
expect(backend.owns_session).to_equal(false)
expect(backend.last_probe.requested_name).to_equal("cuda")
expect(backend.last_probe.api_name).to_equal("cuda")
expect(backend.last_probe.feature_gate).to_equal("cuda_context")
expect(backend.last_probe.status).to_equal(BackendStatus.Failed)
```

</details>

#### rejects active CUDA session replacement without mutating atlas ownership

- rejects active CUDA session replacement without mutating atlas ownership
   - Expected: backend.init_with_session(4, 4, incoming) is false
   - Expected: incoming.ref_count equals `2`
   - Expected: backend.d_font_atlas equals `77`
   - Expected: backend.font_atlas_generation equals `9`
   - Expected: backend.font_atlas_owner_identity equals `old`
   - Expected: backend.owns_session is true
   - Expected: backend.init_with_session(0, 4, invalid) is false
   - Expected: backend.initialized is true
   - Expected: backend.owns_session is true
   - Expected: backend.d_font_atlas equals `77`
   - Expected: invalid.ref_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
expect(backend.init_with_session(4, 4, incoming)).to_equal(false)
expect(incoming.ref_count).to_equal(2)
expect(backend.d_font_atlas).to_equal(77)
expect(backend.font_atlas_generation).to_equal(9)
expect(backend.font_atlas_owner_identity).to_equal("old")
expect(backend.owns_session).to_equal(true)
var invalid = CudaSession.create()
expect(backend.init_with_session(0, 4, invalid)).to_equal(false)
expect(backend.initialized).to_equal(true)
expect(backend.owns_session).to_equal(true)
expect(backend.d_font_atlas).to_equal(77)
expect(invalid.ref_count).to_equal(0)
```

</details>

#### reports CUDA 2D kernel readiness or the real kernel gap

- reports CUDA 2D kernel readiness or the real kernel gap
   - Expected: probe.is_usable() is true
   - Expected: probe.has_compute is true
   - Expected: probe.has_graphics is true
   - Expected: probe.has_present is true
   - Expected: probe.status equals `BackendStatus.Failed`
   - Expected: probe.is_usable() is false
   - Expected: probe.has_compute is true
   - Expected: probe.has_graphics is false
   - Expected: probe.has_present is false
   - Expected: probe.is_usable() equals `probe.status == BackendStatus.Initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports CUDA 2D kernel readiness or the real kernel gap")
val probe = probe_cuda_2d()
if probe.status == BackendStatus.Initialized:
    expect(probe.is_usable()).to_equal(true)
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(true)
    expect(probe.has_present).to_equal(true)
else if probe.feature_gate == "cuda_2d_render":
    expect(probe.status).to_equal(BackendStatus.Failed)
    expect(probe.is_usable()).to_equal(false)
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(false)
    expect(probe.has_present).to_equal(false)
    expect(probe.fallback_reason).to_contain("simple_2d_fill_u32")
    expect(probe.fallback_reason).to_contain("kernel_clear")
    expect(probe.fallback_reason).to_contain("kernel_draw_rect_filled")
    expect(probe.fallback_reason).to_contain("kernel_draw_rect_outline")
    expect(probe.fallback_reason).to_contain("kernel_draw_image")
    expect(probe.fallback_reason).to_contain("kernel_draw_gradient_rect")
    expect(probe.fallback_reason).to_contain("kernel_draw_line")
else:
    # Neither recognised shape. Both branches above are claims about the
    # probe OBJECT (self-consistency), not predictions about a later
    # create, so they stay hard assertions — but a probe that matches
    # neither must not slip through as a silent pass.
    expect(probe.is_usable()).to_equal(probe.status == BackendStatus.Initialized)
    print "[cuda-2d] cuda-2d-readiness: NEITHER SHAPE MATCHED — status is not Initialized and feature_gate is '{probe.feature_gate}', not 'cuda_2d_render'; this example proves NOTHING about the 2D kernel gap"
```

</details>

#### does not mark CUDA usable when the PTX self-test fails

- does not mark CUDA usable when the PTX self-test fails
   - Expected: probe.status equals `BackendStatus.Failed`
   - Expected: probe.is_usable() is false
   - Expected: probe.has_compute is true
   - Expected: probe.has_graphics is false
   - Expected: probe.has_present is false
   - Expected: probe.is_usable() equals `probe.status == BackendStatus.Initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not mark CUDA usable when the PTX self-test fails")
val probe = probe_cuda_2d()
if probe.feature_gate == "cuda_2d_render_self_test":
    expect(probe.status).to_equal(BackendStatus.Failed)
    expect(probe.is_usable()).to_equal(false)
    expect(probe.has_compute).to_equal(true)
    expect(probe.has_graphics).to_equal(false)
    expect(probe.has_present).to_equal(false)
    expect(probe.fallback_reason).to_contain("self-test")
else:
    # The self-test gate was not the one that fired, so the body above
    # never ran. Disclose it instead of reporting a silent pass.
    expect(probe.is_usable()).to_equal(probe.status == BackendStatus.Initialized)
    print "[cuda-2d] cuda-2d-self-test: SELF-TEST GATE NOT EXERCISED — feature_gate is '{probe.feature_gate}', not 'cuda_2d_render_self_test'; this example proves NOTHING about the PTX self-test path"
```

</details>

#### strict Engine2D cuda creation returns typed cuda failure instead of fallback

- strict Engine2D cuda creation returns typed cuda failure instead of fallback
   - Expected: diag.requested_name equals `cuda`
   - Expected: diag.selected_name equals `cuda`
   - Expected: diag.backend_name equals `cuda`
   - Expected: diag.status == BackendStatus.Unavailable or diag.status == BackendStatus.Failed is true
   - Expected: engine.backend_name() equals `cuda`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
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
    expect(diag.requested_name).to_equal("cuda")
    expect(diag.selected_name).to_equal("cuda")
    expect(diag.backend_name).to_equal("cuda")
    expect(diag.status == BackendStatus.Unavailable or diag.status == BackendStatus.Failed).to_equal(true)
    expect(diag.status).to_not_equal(BackendStatus.Fallback)
else:
    # The strictness claim still holds on the success path, so this
    # branch is not a silent skip either.
    var engine = result.unwrap()
    expect(engine.backend_name()).to_equal("cuda")
    engine.shutdown()
    print "[cuda-2d] cuda-strict-typed-failure: FAILURE PATH NOT EXERCISED — the strict cuda create succeeded, so this example proves NOTHING about the typed-failure path"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl` |
| Updated | 2026-08-26 |
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
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `eb23f90ef212834e5c3bf2386a969a4f23ccb701f61712e11129c14ab749f267`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb23f90ef212834e5c3bf2386a969a4f23ccb701f61712e11129c14ab749f267`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb23f90ef212834e5c3bf2386a969a4f23ccb701f61712e11129c14ab749f267`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 23 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fences the atlas cache with CUDA target and session identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares explicit CUDA device and mirror authority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps GPU success and CPU fallback authority transitions explicit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
