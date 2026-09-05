# webgpu_resources_spec

> Purpose: Verify Browser WebGPU resources.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 36 | 36 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# webgpu_resources_spec

Purpose: Verify Browser WebGPU resources.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/webgpu/webgpu_resources_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Browser WebGPU resources.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### Browser WebGPU resources

### resource handles

#### allocates deterministic handles across buffer texture and sampler

- allocates deterministic handles across buffer texture and sampler
- allocates deterministic handles across buffer texture and sampler
   - Expected: buffer.valid is true
   - Expected: buffer.id equals `1`
   - Expected: texture.valid is true
   - Expected: texture.id equals `2`
   - Expected: sampler.valid is true
   - Expected: sampler.id equals `3`
   - Expected: resources.resource_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates deterministic handles across buffer texture and sampler")
step("allocates deterministic handles across buffer texture and sampler")
# @req: REQ-FEAT-WEBGPU-WEBGPU-RESOURCES-SPEC-001
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_COPY_DST | WEBGPU_BUFFER_USAGE_UNIFORM)
val texture = resources.create_texture("albedo", 64, 32, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING | WEBGPU_TEXTURE_USAGE_COPY_DST)
val sampler = resources.create_sampler("nearest", "clamp-to-edge", "repeat", "nearest", "linear")
expect(buffer.valid).to_equal(true)
expect(buffer.id).to_equal(1)
expect(texture.valid).to_equal(true)
expect(texture.id).to_equal(2)
expect(sampler.valid).to_equal(true)
expect(sampler.id).to_equal(3)
expect(resources.resource_count()).to_equal(3)
```

</details>

#### allocates bind group layouts and bind groups after resources

- allocates bind group layouts and bind groups after resources
- allocates bind group layouts and bind groups after resources
   - Expected: layout.valid is true
   - Expected: layout.id equals `4`
   - Expected: layout.entry_count() equals `3`
   - Expected: bind_group.valid is true
   - Expected: bind_group.id equals `5`
   - Expected: bind_group.entry_count() equals `3`
   - Expected: resources.resource_count() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates bind group layouts and bind groups after resources")
step("allocates bind group layouts and bind groups after resources")
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_COPY_DST | WEBGPU_BUFFER_USAGE_UNIFORM)
val texture = resources.create_texture("albedo", 64, 32, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING | WEBGPU_TEXTURE_USAGE_COPY_DST)
val sampler = resources.create_sampler("nearest", "clamp-to-edge", "repeat", "nearest", "linear")
val layout = resources.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.texture(1, WEBGPU_SHADER_STAGE_FRAGMENT),
    GPUBindGroupLayoutEntry.sampler(2, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bind_group = resources.create_bind_group("material-0", layout.id, [
    GPUBindGroupEntry.buffer(0, buffer.id),
    GPUBindGroupEntry.texture(1, texture.id),
    GPUBindGroupEntry.sampler(2, sampler.id)
])
expect(layout.valid).to_equal(true)
expect(layout.id).to_equal(4)
expect(layout.entry_count()).to_equal(3)
expect(bind_group.valid).to_equal(true)
expect(bind_group.id).to_equal(5)
expect(bind_group.entry_count()).to_equal(3)
expect(resources.resource_count()).to_equal(5)
```

</details>

#### allocates bind groups with texture view entries

- allocates bind groups with texture view entries
- allocates bind groups with texture view entries
   - Expected: bind_group.valid is true
   - Expected: bind_group.id equals `4`
   - Expected: bind_group.entries[0].texture_view_id equals `view.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates bind groups with texture view entries")
step("allocates bind groups with texture view entries")
var resources = WebGPUResourceTable.create()
val texture = resources.create_texture_with_dimension("volume", 16, 16, 4, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_3D)
val view = resources.create_texture_view("volume-view", texture.id, "", WEBGPU_TEXTURE_DIMENSION_3D, 0, 1, 0, 4)
val layout = resources.create_bind_group_layout("sampled", [
    GPUBindGroupLayoutEntry.texture(0, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bind_group = resources.create_bind_group("sampled-0", layout.id, [
    GPUBindGroupEntry.texture_view(0, view.id)
])
expect(bind_group.valid).to_equal(true)
expect(bind_group.id).to_equal(4)
expect(bind_group.entries[0].texture_view_id).to_equal(view.id)
```

</details>

#### does not consume an id for invalid resources

- does not consume an id for invalid resources
- does not consume an id for invalid resources
   - Expected: rejected.valid is false
   - Expected: rejected.id equals `-1`
   - Expected: accepted.id equals `1`
   - Expected: resources.resource_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not consume an id for invalid resources")
step("does not consume an id for invalid resources")
var resources = WebGPUResourceTable.create()
val rejected = resources.create_buffer("empty", 0, WEBGPU_BUFFER_USAGE_UNIFORM)
val accepted = resources.create_buffer("uniforms", 16, WEBGPU_BUFFER_USAGE_UNIFORM)
expect(rejected.valid).to_equal(false)
expect(rejected.id).to_equal(-1)
expect(accepted.id).to_equal(1)
expect(resources.resource_count()).to_equal(1)
```

</details>

#### allocates deterministic texture view handles

- allocates deterministic texture view handles
- allocates deterministic texture view handles
   - Expected: texture.id equals `1`
   - Expected: view.valid is true
   - Expected: view.id equals `2`
   - Expected: view.texture_id equals `texture.id`
   - Expected: view.format equals `GPU_TEXTURE_FORMAT_RGBA8_UNORM`
   - Expected: found.valid is true
   - Expected: found.base_mip_level equals `1`
   - Expected: resources.resource_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates deterministic texture view handles")
step("allocates deterministic texture view handles")
var resources = WebGPUResourceTable.create()
val texture = resources.create_texture_with_mip_levels("array", 64, 64, 4, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING | WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_2D, 3)
val view = resources.create_texture_view("array-slice", texture.id, "", WEBGPU_TEXTURE_DIMENSION_2D, 1, 2, 1, 2)
val found = webgpu_find_texture_view(resources, view.id)
expect(texture.id).to_equal(1)
expect(view.valid).to_equal(true)
expect(view.id).to_equal(2)
expect(view.texture_id).to_equal(texture.id)
expect(view.format).to_equal(GPU_TEXTURE_FORMAT_RGBA8_UNORM)
expect(found.valid).to_equal(true)
expect(found.base_mip_level).to_equal(1)
expect(resources.resource_count()).to_equal(2)
```

</details>

#### allocates cube texture views for six square layers

- allocates cube texture views for six square layers
- allocates cube texture views for six square layers
   - Expected: view.valid is true
   - Expected: view.dimension equals `WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE`
   - Expected: view.array_layer_count equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates cube texture views for six square layers")
step("allocates cube texture views for six square layers")
var resources = WebGPUResourceTable.create()
val texture = resources.create_texture("skybox", 128, 128, 6, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
val view = resources.create_texture_view("skybox-view", texture.id, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE, 0, 1, 0, 6)
expect(view.valid).to_equal(true)
expect(view.dimension).to_equal(WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE)
expect(view.array_layer_count).to_equal(6)
```

</details>

#### allocates 3d texture views for 3d texture handles

- allocates 3d texture views for 3d texture handles
- allocates 3d texture views for 3d texture handles
   - Expected: texture.valid is true
   - Expected: texture.dimension equals `WEBGPU_TEXTURE_DIMENSION_3D`
   - Expected: view.valid is true
   - Expected: view.dimension equals `WEBGPU_TEXTURE_DIMENSION_3D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates 3d texture views for 3d texture handles")
step("allocates 3d texture views for 3d texture handles")
var resources = WebGPUResourceTable.create()
val texture = resources.create_texture_with_dimension("volume", 32, 32, 8, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_3D)
val view = resources.create_texture_view("volume-view", texture.id, "", WEBGPU_TEXTURE_DIMENSION_3D, 0, 1, 0, 8)
expect(texture.valid).to_equal(true)
expect(texture.dimension).to_equal(WEBGPU_TEXTURE_DIMENSION_3D)
expect(view.valid).to_equal(true)
expect(view.dimension).to_equal(WEBGPU_TEXTURE_DIMENSION_3D)
```

</details>

#### allocates descriptor-complete samplers

- allocates descriptor-complete samplers
- allocates descriptor-complete samplers
   - Expected: sampler.valid is true
   - Expected: sampler.id equals `1`
   - Expected: sampler.address_mode_w equals `clamp-to-edge`
   - Expected: sampler.mipmap_filter equals `linear`
   - Expected: sampler.lod_min_clamp equals `1.0`
   - Expected: sampler.lod_max_clamp equals `8.0`
   - Expected: sampler.compare equals `less-equal`
   - Expected: sampler.max_anisotropy equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates descriptor-complete samplers")
step("allocates descriptor-complete samplers")
var resources = WebGPUResourceTable.create()
val sampler = resources.create_sampler_with_descriptor("shadow", "repeat", "mirror-repeat", "clamp-to-edge", "linear", "linear", "linear", 1.0, 8.0, "less-equal", 4)
expect(sampler.valid).to_equal(true)
expect(sampler.id).to_equal(1)
expect(sampler.address_mode_w).to_equal("clamp-to-edge")
expect(sampler.mipmap_filter).to_equal("linear")
expect(sampler.lod_min_clamp).to_equal(1.0)
expect(sampler.lod_max_clamp).to_equal(8.0)
expect(sampler.compare).to_equal("less-equal")
expect(sampler.max_anisotropy).to_equal(4)
```

</details>

#### allocates descriptor textures with sample counts

- allocates descriptor textures with sample counts
- allocates descriptor textures with sample counts
   - Expected: texture.valid is true
   - Expected: texture.sample_count equals `4`
   - Expected: texture.mip_level_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("allocates descriptor textures with sample counts")
step("allocates descriptor textures with sample counts")
var resources = WebGPUResourceTable.create()
val texture = resources.create_texture_with_descriptor("msaa-color", 64, 64, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 1, 4)
expect(texture.valid).to_equal(true)
expect(texture.sample_count).to_equal(4)
expect(texture.mip_level_count).to_equal(1)
```

</details>

#### does not consume an id for invalid texture views

- does not consume an id for invalid texture views
- does not consume an id for invalid texture views
   - Expected: rejected.valid is false
   - Expected: rejected.id equals `-1`
   - Expected: accepted.id equals `2`
   - Expected: resources.resource_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not consume an id for invalid texture views")
step("does not consume an id for invalid texture views")
var resources = WebGPUResourceTable.create()
val texture = resources.create_texture("albedo", 64, 64, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
val rejected = resources.create_texture_view("bad", texture.id, "bgra8unorm", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 0, 1)
val accepted = resources.create_texture_view("ok", texture.id, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 0, 1)
expect(rejected.valid).to_equal(false)
expect(rejected.id).to_equal(-1)
expect(accepted.id).to_equal(2)
expect(resources.resource_count()).to_equal(2)
```

</details>

### descriptor validation

#### rejects non-positive buffer sizes

- rejects non-positive buffer sizes
- rejects non-positive buffer sizes
   - Expected: webgpu_validate_buffer_descriptor(0, WEBGPU_BUFFER_USAGE_UNIFORM) equals `GPUBuffer size must be positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-positive buffer sizes")
step("rejects non-positive buffer sizes")
expect(webgpu_validate_buffer_descriptor(0, WEBGPU_BUFFER_USAGE_UNIFORM)).to_equal("GPUBuffer size must be positive")
```

</details>

#### rejects unsupported buffer usage bits

- rejects unsupported buffer usage bits
- rejects unsupported buffer usage bits
   - Expected: webgpu_validate_buffer_descriptor(64, 2048) equals `GPUBuffer usage is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported buffer usage bits")
step("rejects unsupported buffer usage bits")
expect(webgpu_validate_buffer_descriptor(64, 2048)).to_equal("GPUBuffer usage is not supported")
```

</details>

#### rejects non-positive texture sizes

- rejects non-positive texture sizes
- rejects non-positive texture sizes
   - Expected: err equals `GPUTexture size must be positive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects non-positive texture sizes")
step("rejects non-positive texture sizes")
val err = webgpu_validate_texture_descriptor(16, 0, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
expect(err).to_equal("GPUTexture size must be positive")
```

</details>

#### rejects unsupported texture formats

- rejects unsupported texture formats
- rejects unsupported texture formats
   - Expected: err equals `GPUTexture format is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported texture formats")
step("rejects unsupported texture formats")
val err = webgpu_validate_texture_descriptor(16, 16, 1, "bc7-rgba-unorm", WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
expect(err).to_equal("GPUTexture format is not supported")
```

</details>

#### accepts depth-stencil texture formats

- accepts depth-stencil texture formats
- accepts depth-stencil texture formats
   - Expected: err equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts depth-stencil texture formats")
step("accepts depth-stencil texture formats")
val err = webgpu_validate_texture_descriptor(16, 16, 1, GPU_TEXTURE_FORMAT_DEPTH24_PLUS_STENCIL8, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
expect(err).to_equal("")
```

</details>

#### rejects unsupported texture usage bits

- rejects unsupported texture usage bits
- rejects unsupported texture usage bits
   - Expected: err equals `GPUTexture usage is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported texture usage bits")
step("rejects unsupported texture usage bits")
val err = webgpu_validate_texture_descriptor(16, 16, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, 64)
expect(err).to_equal("GPUTexture usage is not supported")
```

</details>

#### accepts M26 texture descriptors for 3d arrays msaa and cubemaps

- accepts M26 texture descriptors for 3d arrays msaa and cubemaps
- accepts M26 texture descriptors for 3d arrays msaa and cubemaps
   - Expected: tex3d equals ``
   - Expected: msaa equals ``
   - Expected: cube equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts M26 texture descriptors for 3d arrays msaa and cubemaps")
step("accepts M26 texture descriptors for 3d arrays msaa and cubemaps")
val tex3d = webgpu_validate_extended_texture_descriptor(32, 32, 8, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_3D, 1, 1, WEBGPU_TEXTURE_DIMENSION_3D)
val msaa = webgpu_validate_extended_texture_descriptor(64, 64, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 1, 4, WEBGPU_TEXTURE_DIMENSION_2D)
val cube = webgpu_validate_extended_texture_descriptor(128, 128, 6, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 1, 1, WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE)
expect(tex3d).to_equal("")
expect(msaa).to_equal("")
expect(cube).to_equal("")
```

</details>

#### rejects invalid M26 texture descriptor combinations

- rejects invalid M26 texture descriptor combinations
- rejects invalid M26 texture descriptor combinations
   - Expected: bad_msaa_mips equals `GPUTexture multisampled textures must have one mip level`
   - Expected: bad_msaa_layers equals `GPUTexture multisampling requires one array layer`
   - Expected: bad_cube_layers equals `GPUTexture cube views require exactly six array layers`
   - Expected: bad_cube_shape equals `GPUTexture cube views require square faces`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid M26 texture descriptor combinations")
step("rejects invalid M26 texture descriptor combinations")
val bad_msaa_mips = webgpu_validate_extended_texture_descriptor(64, 64, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 2, 4, WEBGPU_TEXTURE_DIMENSION_2D)
val bad_msaa_layers = webgpu_validate_extended_texture_descriptor(64, 64, 2, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 1, 4, WEBGPU_TEXTURE_DIMENSION_2D)
val bad_cube_layers = webgpu_validate_extended_texture_descriptor(128, 128, 5, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 1, 1, WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE)
val bad_cube_shape = webgpu_validate_extended_texture_descriptor(128, 64, 6, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 1, 1, WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE)
expect(bad_msaa_mips).to_equal("GPUTexture multisampled textures must have one mip level")
expect(bad_msaa_layers).to_equal("GPUTexture multisampling requires one array layer")
expect(bad_cube_layers).to_equal("GPUTexture cube views require exactly six array layers")
expect(bad_cube_shape).to_equal("GPUTexture cube views require square faces")
```

</details>

#### rejects texture mip counts beyond descriptor dimensions

- rejects texture mip counts beyond descriptor dimensions
- rejects texture mip counts beyond descriptor dimensions
   - Expected: too_many_2d_mips equals `GPUTexture mipLevelCount exceeds texture size`
   - Expected: too_many_3d_mips equals `GPUTexture mipLevelCount exceeds texture size`
   - Expected: max_2d_mips equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects texture mip counts beyond descriptor dimensions")
step("rejects texture mip counts beyond descriptor dimensions")
val too_many_2d_mips = webgpu_validate_extended_texture_descriptor(8, 4, 12, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 5, 1, WEBGPU_TEXTURE_DIMENSION_2D)
val too_many_3d_mips = webgpu_validate_extended_texture_descriptor(8, 4, 2, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_3D, 5, 1, WEBGPU_TEXTURE_DIMENSION_3D)
val max_2d_mips = webgpu_validate_extended_texture_descriptor(8, 4, 12, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING, WEBGPU_TEXTURE_DIMENSION_2D, 4, 1, WEBGPU_TEXTURE_DIMENSION_2D)
expect(too_many_2d_mips).to_equal("GPUTexture mipLevelCount exceeds texture size")
expect(too_many_3d_mips).to_equal("GPUTexture mipLevelCount exceeds texture size")
expect(max_2d_mips).to_equal("")
```

</details>

#### rejects invalid texture view descriptor ranges

- rejects invalid texture view descriptor ranges
- rejects invalid texture view descriptor ranges
   - Expected: webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, -1, 1, 0, 1) equals `GPUTextureView baseMipLevel must be non-negative`
   - Expected: webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 0, 0, 1) equals `GPUTextureView mipLevelCount must be positive`
   - Expected: webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 4, 2, 0, 1) equals `GPUTextureView mip range exceeds texture mip levels`
   - Expected: webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, -1, 1) equals `GPUTextureView baseArrayLayer must be non-negative`
   - Expected: webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 0, 0) equals `GPUTextureView arrayLayerCount must be positive`
   - Expected: webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 3, 2) equals `GPUTextureView array layer range exceeds texture layers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid texture view descriptor ranges")
step("rejects invalid texture view descriptor ranges")
var resources = WebGPUResourceTable.create()
val texture = resources.create_texture("array", 16, 16, 4, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
expect(webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, -1, 1, 0, 1)).to_equal("GPUTextureView baseMipLevel must be non-negative")
expect(webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 0, 0, 1)).to_equal("GPUTextureView mipLevelCount must be positive")
expect(webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 4, 2, 0, 1)).to_equal("GPUTextureView mip range exceeds texture mip levels")
expect(webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, -1, 1)).to_equal("GPUTextureView baseArrayLayer must be non-negative")
expect(webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 0, 0)).to_equal("GPUTextureView arrayLayerCount must be positive")
expect(webgpu_validate_texture_view_descriptor(texture, "", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 3, 2)).to_equal("GPUTextureView array layer range exceeds texture layers")
```

</details>

#### rejects invalid texture view format dimension and cube descriptors

- rejects invalid texture view format dimension and cube descriptors
- rejects invalid texture view format dimension and cube descriptors
   - Expected: webgpu_validate_texture_view_descriptor(square, "bgra8unorm", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 0, 1) equals `GPUTextureView format must match texture format`
   - Expected: webgpu_validate_texture_view_descriptor(square, "", WEBGPU_TEXTURE_DIMENSION_3D, 0, 1, 0, 1) equals `GPUTextureView dimension must match texture dimension`
   - Expected: webgpu_validate_texture_view_descriptor(square, "", WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE, 0, 1, 0, 5) equals `GPUTextureView cube views require exactly six array layers`
   - Expected: webgpu_validate_texture_view_descriptor(rectangle, "", WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE, 0, 1, 0, 6) equals `GPUTextureView cube views require square faces`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid texture view format dimension and cube descriptors")
step("rejects invalid texture view format dimension and cube descriptors")
var resources = WebGPUResourceTable.create()
val square = resources.create_texture("skybox", 64, 64, 6, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
val rectangle = resources.create_texture("bad-skybox", 64, 32, 6, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
expect(webgpu_validate_texture_view_descriptor(square, "bgra8unorm", WEBGPU_TEXTURE_DIMENSION_2D, 0, 1, 0, 1)).to_equal("GPUTextureView format must match texture format")
expect(webgpu_validate_texture_view_descriptor(square, "", WEBGPU_TEXTURE_DIMENSION_3D, 0, 1, 0, 1)).to_equal("GPUTextureView dimension must match texture dimension")
expect(webgpu_validate_texture_view_descriptor(square, "", WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE, 0, 1, 0, 5)).to_equal("GPUTextureView cube views require exactly six array layers")
expect(webgpu_validate_texture_view_descriptor(rectangle, "", WEBGPU_TEXTURE_VIEW_DIMENSION_CUBE, 0, 1, 0, 6)).to_equal("GPUTextureView cube views require square faces")
```

</details>

#### rejects unsupported sampler modes

- rejects unsupported sampler modes
- rejects unsupported sampler modes
   - Expected: err equals `GPUSampler address mode is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported sampler modes")
step("rejects unsupported sampler modes")
val err = webgpu_validate_sampler_descriptor("wrap", "repeat", "clamp-to-edge", "nearest", "linear", "nearest", 0.0, 32.0, "", 1)
expect(err).to_equal("GPUSampler address mode is not supported")
```

</details>

#### rejects invalid descriptor-complete sampler fields

- rejects invalid descriptor-complete sampler fields
- rejects invalid descriptor-complete sampler fields
   - Expected: webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "cubic", 0.0, 32.0, "", 1) equals `GPUSampler filter mode is not supported`
   - Expected: webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "nearest", 4.0, 2.0, "", 1) equals `GPUSampler lod clamp range is invalid`
   - Expected: webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "nearest", 0.0, 32.0, "between", 1) equals `GPUSampler compare function is not supported`
   - Expected: webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "nearest", 0.0, 32.0, "", 0) equals `GPUSampler maxAnisotropy must be at least 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid descriptor-complete sampler fields")
step("rejects invalid descriptor-complete sampler fields")
expect(webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "cubic", 0.0, 32.0, "", 1)).to_equal("GPUSampler filter mode is not supported")
expect(webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "nearest", 4.0, 2.0, "", 1)).to_equal("GPUSampler lod clamp range is invalid")
expect(webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "nearest", 0.0, 32.0, "between", 1)).to_equal("GPUSampler compare function is not supported")
expect(webgpu_validate_sampler_descriptor("repeat", "repeat", "repeat", "nearest", "linear", "nearest", 0.0, 32.0, "", 0)).to_equal("GPUSampler maxAnisotropy must be at least 1")
```

</details>

#### rejects duplicate bind group layout bindings

- rejects duplicate bind group layout bindings
- rejects duplicate bind group layout bindings
   - Expected: err equals `GPUBindGroupLayout bindings must be unique`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects duplicate bind group layout bindings")
step("rejects duplicate bind group layout bindings")
val err = webgpu_validate_bind_group_layout_descriptor([
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
])
expect(err).to_equal("GPUBindGroupLayout bindings must be unique")
```

</details>

#### rejects unsupported bind group layout visibility

- rejects unsupported bind group layout visibility
- rejects unsupported bind group layout visibility
   - Expected: err equals `GPUBindGroupLayout visibility is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported bind group layout visibility")
step("rejects unsupported bind group layout visibility")
val err = webgpu_validate_bind_group_layout_descriptor([
    GPUBindGroupLayoutEntry.buffer(0, 16)
])
expect(err).to_equal("GPUBindGroupLayout visibility is not supported")
```

</details>

#### rejects unsupported bind group layout binding type

- rejects unsupported bind group layout binding type
- rejects unsupported bind group layout binding type
   - Expected: err equals `GPUBindGroupLayout binding type is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported bind group layout binding type")
step("rejects unsupported bind group layout binding type")
val err = webgpu_validate_bind_group_layout_descriptor([
    GPUBindGroupLayoutEntry(binding: 0, visibility: WEBGPU_SHADER_STAGE_VERTEX, binding_type: 99, has_dynamic_offset: false)
])
expect(err).to_equal("GPUBindGroupLayout binding type is not supported")
```

</details>

#### creates storage-specific bind group layout entries

- creates storage-specific bind group layout entries
- creates storage-specific bind group layout entries
   - Expected: err equals ``
   - Expected: readonly.binding_type equals `WEBGPU_BINDING_TYPE_READONLY_STORAGE_BUFFER`
   - Expected: storage_texture.binding_type equals `WEBGPU_BINDING_TYPE_STORAGE_TEXTURE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates storage-specific bind group layout entries")
step("creates storage-specific bind group layout entries")
val readonly = GPUBindGroupLayoutEntry.readonly_storage_buffer(0, WEBGPU_SHADER_STAGE_VERTEX)
val storage_texture = GPUBindGroupLayoutEntry.storage_texture(1, WEBGPU_SHADER_STAGE_FRAGMENT)
val err = webgpu_validate_bind_group_layout_descriptor([readonly, storage_texture])
expect(err).to_equal("")
expect(readonly.binding_type).to_equal(WEBGPU_BINDING_TYPE_READONLY_STORAGE_BUFFER)
expect(storage_texture.binding_type).to_equal(WEBGPU_BINDING_TYPE_STORAGE_TEXTURE)
```

</details>

#### creates sampler layout entries for filtering non-filtering and comparison samplers

- creates sampler layout entries for filtering non-filtering and comparison samplers
- creates sampler layout entries for filtering non-filtering and comparison samplers
   - Expected: filtering.binding_type equals `6`
   - Expected: nearest.binding_type equals `WEBGPU_BINDING_TYPE_NON_FILTERING_SAMPLER`
   - Expected: comparison.binding_type equals `WEBGPU_BINDING_TYPE_COMPARISON_SAMPLER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates sampler layout entries for filtering non-filtering and comparison samplers")
step("creates sampler layout entries for filtering non-filtering and comparison samplers")
val filtering = GPUBindGroupLayoutEntry.sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
val nearest = GPUBindGroupLayoutEntry.non_filtering_sampler(1, WEBGPU_SHADER_STAGE_FRAGMENT)
val comparison = GPUBindGroupLayoutEntry.comparison_sampler(2, WEBGPU_SHADER_STAGE_FRAGMENT)
expect(filtering.binding_type).to_equal(6)
expect(nearest.binding_type).to_equal(WEBGPU_BINDING_TYPE_NON_FILTERING_SAMPLER)
expect(comparison.binding_type).to_equal(WEBGPU_BINDING_TYPE_COMPARISON_SAMPLER)
```

</details>

#### accepts dynamic offsets only for buffer layout bindings

- accepts dynamic offsets only for buffer layout bindings
- accepts dynamic offsets only for buffer layout bindings
   - Expected: ok equals ``
   - Expected: bad equals `GPUBindGroupLayout dynamic offsets require buffer bindings`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts dynamic offsets only for buffer layout bindings")
step("accepts dynamic offsets only for buffer layout bindings")
val ok = webgpu_validate_bind_group_layout_descriptor([
    GPUBindGroupLayoutEntry.dynamic_buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.dynamic_storage_buffer(1, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bad = webgpu_validate_bind_group_layout_descriptor([
    GPUBindGroupLayoutEntry(binding: 0, visibility: WEBGPU_SHADER_STAGE_FRAGMENT, binding_type: 6, has_dynamic_offset: true)
])
expect(ok).to_equal("")
expect(bad).to_equal("GPUBindGroupLayout dynamic offsets require buffer bindings")
```

</details>

#### rejects bind groups with missing layout bindings

- rejects bind groups with missing layout bindings
- rejects bind groups with missing layout bindings
   - Expected: bind_group.valid is false
   - Expected: bind_group.error equals `GPUBindGroup entry count must match layout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects bind groups with missing layout bindings")
step("rejects bind groups with missing layout bindings")
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_UNIFORM)
val layout = resources.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.sampler(1, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bind_group = resources.create_bind_group("bad", layout.id, [
    GPUBindGroupEntry.buffer(0, buffer.id)
])
expect(bind_group.valid).to_equal(false)
expect(bind_group.error).to_equal("GPUBindGroup entry count must match layout")
```

</details>

#### rejects bind group entries with duplicate bindings

- rejects bind group entries with duplicate bindings
- rejects bind group entries with duplicate bindings
   - Expected: bind_group.valid is false
   - Expected: bind_group.error equals `GPUBindGroup bindings must be unique`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects bind group entries with duplicate bindings")
step("rejects bind group entries with duplicate bindings")
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_UNIFORM)
val sampler = resources.create_sampler("nearest", "clamp-to-edge", "repeat", "nearest", "linear")
val layout = resources.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.sampler(1, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bind_group = resources.create_bind_group("bad", layout.id, [
    GPUBindGroupEntry.buffer(0, buffer.id),
    GPUBindGroupEntry.sampler(0, sampler.id)
])
expect(bind_group.valid).to_equal(false)
expect(bind_group.error).to_equal("GPUBindGroup bindings must be unique")
```

</details>

#### rejects bind group entries with negative bindings

- rejects bind group entries with negative bindings
- rejects bind group entries with negative bindings
   - Expected: bind_group.valid is false
   - Expected: bind_group.error equals `GPUBindGroup binding must be non-negative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects bind group entries with negative bindings")
step("rejects bind group entries with negative bindings")
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_UNIFORM)
val layout = resources.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX)
])
val bind_group = resources.create_bind_group("bad", layout.id, [
    GPUBindGroupEntry.buffer(-1, buffer.id)
])
expect(bind_group.valid).to_equal(false)
expect(bind_group.error).to_equal("GPUBindGroup binding must be non-negative")
```

</details>

#### rejects bind groups that bind the wrong resource class

- rejects bind groups that bind the wrong resource class
- rejects bind groups that bind the wrong resource class
   - Expected: bind_group.valid is false
   - Expected: bind_group.error equals `GPUBindGroup sampler binding must reference a sampler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects bind groups that bind the wrong resource class")
step("rejects bind groups that bind the wrong resource class")
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_UNIFORM)
val layout = resources.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bind_group = resources.create_bind_group("bad", layout.id, [
    GPUBindGroupEntry.buffer(0, buffer.id)
])
expect(bind_group.valid).to_equal(false)
expect(bind_group.error).to_equal("GPUBindGroup sampler binding must reference a sampler")
```

</details>

#### validates bind group buffer binding ranges

- validates bind group buffer binding ranges
- validates bind group buffer binding ranges
   - Expected: ok.valid is true
   - Expected: ok.entries[0].buffer_offset equals `64`
   - Expected: ok.entries[0].buffer_size equals `128`
   - Expected: negative.valid is false
   - Expected: negative.error equals `GPUBindGroup buffer offset must be non-negative`
   - Expected: zero_size.valid is false
   - Expected: zero_size.error equals `GPUBindGroup buffer binding size must be positive`
   - Expected: overflow.valid is false
   - Expected: overflow.error equals `GPUBindGroup buffer binding range exceeds buffer size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("validates bind group buffer binding ranges")
step("validates bind group buffer binding ranges")
var resources = WebGPUResourceTable.create()
val buffer = resources.create_buffer("uniforms", 256, WEBGPU_BUFFER_USAGE_UNIFORM)
val layout = resources.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX)
])
val ok = resources.create_bind_group("ok", layout.id, [
    GPUBindGroupEntry.buffer_range(0, buffer.id, 64, 128)
])
val negative = resources.create_bind_group("negative", layout.id, [
    GPUBindGroupEntry.buffer_range(0, buffer.id, -1, 16)
])
val zero_size = resources.create_bind_group("zero-size", layout.id, [
    GPUBindGroupEntry.buffer_range(0, buffer.id, 64, 0)
])
val overflow = resources.create_bind_group("overflow", layout.id, [
    GPUBindGroupEntry.buffer_range(0, buffer.id, 192, 128)
])
expect(ok.valid).to_equal(true)
expect(ok.entries[0].buffer_offset).to_equal(64)
expect(ok.entries[0].buffer_size).to_equal(128)
expect(negative.valid).to_equal(false)
expect(negative.error).to_equal("GPUBindGroup buffer offset must be non-negative")
expect(zero_size.valid).to_equal(false)
expect(zero_size.error).to_equal("GPUBindGroup buffer binding size must be positive")
expect(overflow.valid).to_equal(false)
expect(overflow.error).to_equal("GPUBindGroup buffer binding range exceeds buffer size")
```

</details>

#### rejects bind groups with missing texture view resources

- rejects bind groups with missing texture view resources
- rejects bind groups with missing texture view resources
   - Expected: bind_group.valid is false
   - Expected: bind_group.error equals `GPUBindGroup texture view resource does not exist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects bind groups with missing texture view resources")
step("rejects bind groups with missing texture view resources")
var resources = WebGPUResourceTable.create()
val layout = resources.create_bind_group_layout("sampled", [
    GPUBindGroupLayoutEntry.texture(0, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val bind_group = resources.create_bind_group("bad", layout.id, [
    GPUBindGroupEntry.texture_view(0, 99)
])
expect(bind_group.valid).to_equal(false)
expect(bind_group.error).to_equal("GPUBindGroup texture view resource does not exist")
```

</details>

#### validates sampler bindings against filtering comparison and non-filtering layout types

- validates sampler bindings against filtering comparison and non-filtering layout types
- validates sampler bindings against filtering comparison and non-filtering layout types
   - Expected: resources.create_bind_group("filtering-ok", filtering_layout.id, [GPUBindGroupEntry.sampler(0, filtering.id)]).valid is true
   - Expected: resources.create_bind_group("nearest-ok", nearest_layout.id, [GPUBindGroupEntry.sampler(0, nearest.id)]).valid is true
   - Expected: resources.create_bind_group("comparison-ok", comparison_layout.id, [GPUBindGroupEntry.sampler(0, comparison.id)]).valid is true
   - Expected: bad_comparison.valid is false
   - Expected: bad_comparison.error equals `GPUBindGroup comparison sampler binding requires a compare sampler`
   - Expected: bad_filtering.valid is false
   - Expected: bad_filtering.error equals `GPUBindGroup filtering sampler binding cannot reference a comparison sampler`
   - Expected: bad_nearest.valid is false
   - Expected: bad_nearest.error equals `GPUBindGroup non-filtering sampler binding requires nearest filters`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("validates sampler bindings against filtering comparison and non-filtering layout types")
step("validates sampler bindings against filtering comparison and non-filtering layout types")
var resources = WebGPUResourceTable.create()
val filtering = resources.create_sampler_with_descriptor("linear", "repeat", "repeat", "repeat", "linear", "linear", "linear", 0.0, 32.0, "", 1)
val nearest = resources.create_sampler_with_descriptor("nearest", "repeat", "repeat", "repeat", "nearest", "nearest", "nearest", 0.0, 32.0, "", 1)
val comparison = resources.create_sampler_with_descriptor("shadow", "clamp-to-edge", "clamp-to-edge", "clamp-to-edge", "linear", "linear", "linear", 0.0, 32.0, "less-equal", 1)
val filtering_layout = resources.create_bind_group_layout("filtering", [
    GPUBindGroupLayoutEntry.sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val nearest_layout = resources.create_bind_group_layout("nearest", [
    GPUBindGroupLayoutEntry.non_filtering_sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val comparison_layout = resources.create_bind_group_layout("comparison", [
    GPUBindGroupLayoutEntry.comparison_sampler(0, WEBGPU_SHADER_STAGE_FRAGMENT)
])
expect(resources.create_bind_group("filtering-ok", filtering_layout.id, [GPUBindGroupEntry.sampler(0, filtering.id)]).valid).to_equal(true)
expect(resources.create_bind_group("nearest-ok", nearest_layout.id, [GPUBindGroupEntry.sampler(0, nearest.id)]).valid).to_equal(true)
expect(resources.create_bind_group("comparison-ok", comparison_layout.id, [GPUBindGroupEntry.sampler(0, comparison.id)]).valid).to_equal(true)
val bad_comparison = resources.create_bind_group("comparison-bad", comparison_layout.id, [GPUBindGroupEntry.sampler(0, filtering.id)])
val bad_filtering = resources.create_bind_group("filtering-bad", filtering_layout.id, [GPUBindGroupEntry.sampler(0, comparison.id)])
val bad_nearest = resources.create_bind_group("nearest-bad", nearest_layout.id, [GPUBindGroupEntry.sampler(0, filtering.id)])
expect(bad_comparison.valid).to_equal(false)
expect(bad_comparison.error).to_equal("GPUBindGroup comparison sampler binding requires a compare sampler")
expect(bad_filtering.valid).to_equal(false)
expect(bad_filtering.error).to_equal("GPUBindGroup filtering sampler binding cannot reference a comparison sampler")
expect(bad_nearest.valid).to_equal(false)
expect(bad_nearest.error).to_equal("GPUBindGroup non-filtering sampler binding requires nearest filters")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 36 |
| Active scenarios | 36 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-WEBGPU-WEBGPU-RESOURCES-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68cb36498cc4669fb9a0da586c7d6d5a93bbd944bcd543e47d8e5fb93a217779`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68cb36498cc4669fb9a0da586c7d6d5a93bbd944bcd543e47d8e5fb93a217779`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68cb36498cc4669fb9a0da586c7d6d5a93bbd944bcd543e47d8e5fb93a217779`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/web_platform/webgpu/webgpu_resources_spec.spl
mirror: doc/06_spec/feature/web_platform/webgpu/webgpu_resources_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/webgpu/webgpu_resources_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/webgpu/webgpu_resources_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/webgpu/webgpu_resources_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 30 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/webgpu/webgpu_resources_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates deterministic handles across buffer texture and sampler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgpu/webgpu_resources_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates bind group layouts and bind groups after resources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgpu/webgpu_resources_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates bind groups with texture view entries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
