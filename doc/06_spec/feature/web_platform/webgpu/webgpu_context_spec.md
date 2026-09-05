# webgpu_context_spec

> Purpose: Verify Browser WebGPU context.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 46 | 46 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# webgpu_context_spec

Purpose: Verify Browser WebGPU context.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/webgpu/webgpu_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify Browser WebGPU context.
Audience: QA and feature maintainers reading this spec suite.

## Scenarios

### Browser WebGPU context

### secure context gate

#### does not expose WebGPU in insecure context

- does not expose WebGPU in insecure context
- does not expose WebGPU in insecure context
   - Expected: webgpu_is_available(ctx) is false
   - Expected: ok is false
   - Expected: webgpu_adapter_status(ctx) equals `unavailable: secure context required`
   - Expected: ctx.last_error equals `WebGPU requires a secure context`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("does not expose WebGPU in insecure context")
step("does not expose WebGPU in insecure context")
# @req: REQ-FEAT-WEBGPU-WEBGPU-CONTEXT-SPEC-001
var ctx = webgpu_create_context(false)
expect(webgpu_is_available(ctx)).to_equal(false)
val ok = ctx.request_adapter(GPURequestAdapterOptions.default_options())
expect(ok).to_equal(false)
expect(webgpu_adapter_status(ctx)).to_equal("unavailable: secure context required")
expect(ctx.last_error).to_equal("WebGPU requires a secure context")
```

</details>

#### requests adapter and device in secure context

- requests adapter and device in secure context
- requests adapter and device in secure context
   - Expected: webgpu_is_available(ctx) is true
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: webgpu_adapter_status(ctx) equals `available`
   - Expected: webgpu_compatibility_mode(ctx) is false
   - Expected: ctx.request_device(GPUDeviceDescriptor.with_features([GPU_FEATURE_SHADER_F16])) is true
   - Expected: ctx.device_ready is true
   - Expected: ctx.enabled_features.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("requests adapter and device in secure context")
step("requests adapter and device in secure context")
var ctx = webgpu_create_context(true)
expect(webgpu_is_available(ctx)).to_equal(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(webgpu_adapter_status(ctx)).to_equal("available")
expect(webgpu_compatibility_mode(ctx)).to_equal(false)
expect(ctx.request_device(GPUDeviceDescriptor.with_features([GPU_FEATURE_SHADER_F16]))).to_equal(true)
expect(ctx.device_ready).to_equal(true)
expect(ctx.enabled_features.len()).to_equal(1)
```

</details>

#### reports fallback compatibility mode when requested

- reports fallback compatibility mode when requested
- reports fallback compatibility mode when requested
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.fallback()) is true
   - Expected: webgpu_adapter_status(ctx) equals `available`
   - Expected: webgpu_compatibility_mode(ctx) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports fallback compatibility mode when requested")
step("reports fallback compatibility mode when requested")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.fallback())).to_equal(true)
expect(webgpu_adapter_status(ctx)).to_equal("available")
expect(webgpu_compatibility_mode(ctx)).to_equal(true)
```

</details>

#### rejects unsupported required feature

- rejects unsupported required feature
- rejects unsupported required feature
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.with_features(["unknown-feature"])) is false
   - Expected: ctx.device_ready is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported required feature")
step("rejects unsupported required feature")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.with_features(["unknown-feature"]))).to_equal(false)
expect(ctx.device_ready).to_equal(false)
```

</details>

#### rejects unsupported required limits without readying the device

- rejects unsupported required limits without readying the device
- rejects unsupported required limits without readying the device
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(descriptor) is false
   - Expected: ctx.device_ready is false
   - Expected: ctx.last_error equals `required limit exceeds supported limit: max_buffer_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported required limits without readying the device")
step("rejects unsupported required limits without readying the device")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
var limits = GPUDeviceLimits.defaults()
limits.max_buffer_size = 536870912
var descriptor = GPUDeviceDescriptor.create()
descriptor.required_limits = limits
expect(ctx.request_device(descriptor)).to_equal(false)
expect(ctx.device_ready).to_equal(false)
expect(ctx.last_error).to_equal("required limit exceeds supported limit: max_buffer_size")
```

</details>

### canvas configuration

#### configures preferred WebGPU canvas format

- configures preferred WebGPU canvas format
- configures preferred WebGPU canvas format
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: webgpu_preferred_canvas_format() equals `GPU_TEXTURE_FORMAT_BGRA8_UNORM`
   - Expected: ctx.configure_canvas(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480) is true
   - Expected: ctx.canvas_configured is true
   - Expected: ctx.canvas_config.width equals `640`
   - Expected: ctx.canvas_config.alpha_mode equals `opaque`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("configures preferred WebGPU canvas format")
step("configures preferred WebGPU canvas format")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
expect(webgpu_preferred_canvas_format()).to_equal(GPU_TEXTURE_FORMAT_BGRA8_UNORM)
expect(ctx.configure_canvas(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480)).to_equal(true)
expect(ctx.canvas_configured).to_equal(true)
expect(ctx.canvas_config.width).to_equal(640)
expect(ctx.canvas_config.alpha_mode).to_equal("opaque")
```

</details>

#### supports premultiplied alpha and present after canvas configuration

- supports premultiplied alpha and present after canvas configuration
- supports premultiplied alpha and present after canvas configuration
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.configure_canvas_with_alpha(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480, "premultiplied") is true
   - Expected: ctx.canvas_config.alpha_mode equals `premultiplied`
   - Expected: ctx.present() is true
   - Expected: ctx.present_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports premultiplied alpha and present after canvas configuration")
step("supports premultiplied alpha and present after canvas configuration")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
expect(ctx.configure_canvas_with_alpha(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480, "premultiplied")).to_equal(true)
expect(ctx.canvas_config.alpha_mode).to_equal("premultiplied")
expect(ctx.present()).to_equal(true)
expect(ctx.present_count).to_equal(1)
```

</details>

#### rejects unsupported alpha modes and present before configure

- rejects unsupported alpha modes and present before configure
- rejects unsupported alpha modes and present before configure
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.present() is false
   - Expected: ctx.last_error equals `configure must succeed before present`
   - Expected: ctx.configure_canvas_with_alpha(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480, "straight") is false
   - Expected: ctx.last_error equals `unsupported WebGPU alpha mode: straight`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unsupported alpha modes and present before configure")
step("rejects unsupported alpha modes and present before configure")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
expect(ctx.present()).to_equal(false)
expect(ctx.last_error).to_equal("configure must succeed before present")
expect(ctx.configure_canvas_with_alpha(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480, "straight")).to_equal(false)
expect(ctx.last_error).to_equal("unsupported WebGPU alpha mode: straight")
```

</details>

#### rejects zero-sized canvas

- rejects zero-sized canvas
- rejects zero-sized canvas
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.configure_canvas(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 0, 480) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects zero-sized canvas")
step("rejects zero-sized canvas")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
expect(ctx.configure_canvas(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 0, 480)).to_equal(false)
```

</details>

### WGSL validation

#### accepts vertex fragment and compute stages

- accepts vertex fragment and compute stages
- accepts vertex fragment and compute stages
   - Expected: webgpu_validate_wgsl(_vertex_wgsl()) equals ``
   - Expected: webgpu_validate_wgsl(_fragment_wgsl()) equals ``
   - Expected: webgpu_validate_wgsl(_compute_wgsl()) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accepts vertex fragment and compute stages")
step("accepts vertex fragment and compute stages")
expect(webgpu_validate_wgsl(_vertex_wgsl())).to_equal("")
expect(webgpu_validate_wgsl(_fragment_wgsl())).to_equal("")
expect(webgpu_validate_wgsl(_compute_wgsl())).to_equal("")
```

</details>

#### rejects GLSL syntax

- rejects GLSL syntax
- rejects GLSL syntax
   - Expected: err equals `WGSL source must not use GLSL syntax`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects GLSL syntax")
step("rejects GLSL syntax")
val err = webgpu_validate_wgsl("#version 300 es\nvoid main() {}")
expect(err).to_equal("WGSL source must not use GLSL syntax")
```

</details>

#### rejects unbalanced braces

- rejects unbalanced braces
- rejects unbalanced braces
   - Expected: err equals `WGSL braces are unbalanced`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects unbalanced braces")
step("rejects unbalanced braces")
val err = webgpu_validate_wgsl("@vertex fn main() -> @builtin(position) vec4f {")
expect(err).to_equal("WGSL braces are unbalanced")
```

</details>

#### rejects missing stage interface declarations

- rejects missing stage interface declarations
- rejects missing stage interface declarations
   - Expected: webgpu_validate_wgsl("@vertex fn main() -> vec4f { return vec4f(0.0); }") equals `WGSL vertex stage must write @builtin(position)`
   - Expected: webgpu_validate_wgsl("@fragment fn main() -> vec4f { return vec4f(1.0); }") equals `WGSL fragment stage must declare @location(0) output`
   - Expected: webgpu_validate_wgsl("@compute fn main() { }") equals `WGSL compute stage must declare @workgroup_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects missing stage interface declarations")
step("rejects missing stage interface declarations")
expect(webgpu_validate_wgsl("@vertex fn main() -> vec4f { return vec4f(0.0); }")).to_equal("WGSL vertex stage must write @builtin(position)")
expect(webgpu_validate_wgsl("@fragment fn main() -> vec4f { return vec4f(1.0); }")).to_equal("WGSL fragment stage must declare @location(0) output")
expect(webgpu_validate_wgsl("@compute fn main() { }")).to_equal("WGSL compute stage must declare @workgroup_size")
```

</details>

#### rejects invalid compute workgroup_size values

- rejects invalid compute workgroup_size values
- rejects invalid compute workgroup_size values
   - Expected: webgpu_validate_wgsl("@compute @workgroup_size(0) fn main() { }") equals `WGSL compute stage must use positive integer workgroup_size components`
   - Expected: webgpu_validate_wgsl("@compute @workgroup_size(-1, 1, 1) fn main() { }") equals `WGSL compute stage must use positive integer workgroup_size components`
   - Expected: webgpu_validate_wgsl("@compute @workgroup_size(1, 2, 3, 4) fn main() { }") equals `WGSL compute stage must use one to three workgroup_size components`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid compute workgroup_size values")
step("rejects invalid compute workgroup_size values")
expect(webgpu_validate_wgsl("@compute @workgroup_size(0) fn main() { }")).to_equal("WGSL compute stage must use positive integer workgroup_size components")
expect(webgpu_validate_wgsl("@compute @workgroup_size(-1, 1, 1) fn main() { }")).to_equal("WGSL compute stage must use positive integer workgroup_size components")
expect(webgpu_validate_wgsl("@compute @workgroup_size(1, 2, 3, 4) fn main() { }")).to_equal("WGSL compute stage must use one to three workgroup_size components")
```

</details>

#### rejects workgroup_size on non-compute stages

- rejects workgroup_size on non-compute stages
- rejects workgroup_size on non-compute stages
   - Expected: webgpu_validate_wgsl("@vertex @workgroup_size(1) fn main() -> @builtin(position) vec4f { return vec4f(0.0); }") equals `WGSL vertex stage must not use @workgroup_size`
   - Expected: webgpu_validate_wgsl("@fragment @workgroup_size(1) fn main() -> @location(0) vec4f { return vec4f(1.0); }") equals `WGSL fragment stage must not use @workgroup_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects workgroup_size on non-compute stages")
step("rejects workgroup_size on non-compute stages")
expect(webgpu_validate_wgsl("@vertex @workgroup_size(1) fn main() -> @builtin(position) vec4f { return vec4f(0.0); }")).to_equal("WGSL vertex stage must not use @workgroup_size")
expect(webgpu_validate_wgsl("@fragment @workgroup_size(1) fn main() -> @location(0) vec4f { return vec4f(1.0); }")).to_equal("WGSL fragment stage must not use @workgroup_size")
```

</details>

#### rejects compute workgroup_size values above device limits

- rejects compute workgroup_size values above device limits
- rejects compute workgroup_size values above device limits
   - Expected: webgpu_validate_wgsl("@compute @workgroup_size(257, 1, 1) fn main() { }") equals `WGSL compute workgroup_size x exceeds device limit`
   - Expected: webgpu_validate_wgsl("@compute @workgroup_size(1, 257, 1) fn main() { }") equals `WGSL compute workgroup_size y exceeds device limit`
   - Expected: webgpu_validate_wgsl("@compute @workgroup_size(1, 1, 65) fn main() { }") equals `WGSL compute workgroup_size z exceeds device limit`
   - Expected: webgpu_validate_wgsl("@compute @workgroup_size(16, 16, 2) fn main() { }") equals `WGSL compute workgroup_size invocations exceed device limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects compute workgroup_size values above device limits")
step("rejects compute workgroup_size values above device limits")
expect(webgpu_validate_wgsl("@compute @workgroup_size(257, 1, 1) fn main() { }")).to_equal("WGSL compute workgroup_size x exceeds device limit")
expect(webgpu_validate_wgsl("@compute @workgroup_size(1, 257, 1) fn main() { }")).to_equal("WGSL compute workgroup_size y exceeds device limit")
expect(webgpu_validate_wgsl("@compute @workgroup_size(1, 1, 65) fn main() { }")).to_equal("WGSL compute workgroup_size z exceeds device limit")
expect(webgpu_validate_wgsl("@compute @workgroup_size(16, 16, 2) fn main() { }")).to_equal("WGSL compute workgroup_size invocations exceed device limit")
```

</details>

#### rejects mixed-stage modules for the single-entry MVP context

- rejects mixed-stage modules for the single-entry MVP context
- rejects mixed-stage modules for the single-entry MVP context
   - Expected: webgpu_validate_wgsl(source) equals `WGSL source must declare exactly one shader stage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects mixed-stage modules for the single-entry MVP context")
step("rejects mixed-stage modules for the single-entry MVP context")
val source = _vertex_wgsl() + "\n" + _fragment_wgsl()
expect(webgpu_validate_wgsl(source)).to_equal("WGSL source must declare exactly one shader stage")
```

</details>

#### reports structured WGSL diagnostics for console surfaces

- reports structured WGSL diagnostics for console surfaces
- reports structured WGSL diagnostics for console surfaces
   - Expected: diagnostic.severity equals `error`
   - Expected: diagnostic.stage equals `fragment`
   - Expected: diagnostic.line equals `2`
   - Expected: diagnostic.column equals `1`
   - Expected: diagnostic.message equals `WGSL fragment stage must declare @location(0) output`
   - Expected: diagnostic.formatted() equals `error: WGSL fragment shader line 2:1: WGSL fragment stage must declare @locat... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports structured WGSL diagnostics for console surfaces")
step("reports structured WGSL diagnostics for console surfaces")
val source = "// prelude\n@fragment fn main() -> vec4f { return vec4f(1.0); }"
val diagnostic = webgpu_diagnose_wgsl(source)
expect(diagnostic.severity).to_equal("error")
expect(diagnostic.stage).to_equal("fragment")
expect(diagnostic.line).to_equal(2)
expect(diagnostic.column).to_equal(1)
expect(diagnostic.message).to_equal("WGSL fragment stage must declare @location(0) output")
expect(diagnostic.formatted()).to_equal("error: WGSL fragment shader line 2:1: WGSL fragment stage must declare @location(0) output")
```

</details>

#### derives diagnostics from invalid shader modules

- derives diagnostics from invalid shader modules
- derives diagnostics from invalid shader modules
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: module.valid is false
   - Expected: diagnostic.severity equals `error`
   - Expected: diagnostic.line equals `2`
   - Expected: diagnostic.message equals `module.error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("derives diagnostics from invalid shader modules")
step("derives diagnostics from invalid shader modules")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val module = ctx.create_shader_module("bad-fragment", "// prelude\n@fragment fn main() -> vec4f { return vec4f(1.0); }")
val diagnostic = webgpu_shader_module_diagnostic(module)
expect(module.valid).to_equal(false)
expect(diagnostic.severity).to_equal("error")
expect(diagnostic.line).to_equal(2)
expect(diagnostic.message).to_equal(module.error)
```

</details>

#### reflects WGSL bind group resource declarations

- reflects WGSL bind group resource declarations
- reflects WGSL bind group resource declarations
   - Expected: bindings.len() equals `3`
   - Expected: bindings[0].group equals `0`
   - Expected: bindings[0].binding equals `0`
   - Expected: bindings[0].resource_type equals `uniform-buffer`
   - Expected: bindings[0].visibility equals `fragment`
   - Expected: bindings[1].resource_type equals `texture`
   - Expected: bindings[2].resource_type equals `sampler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reflects WGSL bind group resource declarations")
step("reflects WGSL bind group resource declarations")
val source = "@fragment fn main(@location(0) uv: vec2f) -> @location(0) vec4f {\n  return vec4f(1.0);\n}\n@group(0) @binding(0) var<uniform> camera: mat4x4f;\n@group(0) @binding(1) var diffuse: texture_2d<f32>;\n@group(0) @binding(2) var nearest_sampler: sampler;"
val bindings = webgpu_reflect_wgsl_bindings(source)
expect(bindings.len()).to_equal(3)
expect(bindings[0].group).to_equal(0)
expect(bindings[0].binding).to_equal(0)
expect(bindings[0].resource_type).to_equal("uniform-buffer")
expect(bindings[0].visibility).to_equal("fragment")
expect(bindings[1].resource_type).to_equal("texture")
expect(bindings[2].resource_type).to_equal("sampler")
```

</details>

#### reflects WGSL bindings with comments and attribute order variants

- reflects WGSL bindings with comments and attribute order variants
- reflects WGSL bindings with comments and attribute order variants
   - Expected: bindings.len() equals `2`
   - Expected: bindings[0].binding equals `1`
   - Expected: bindings[0].resource_type equals `texture`
   - Expected: bindings[1].binding equals `2`
   - Expected: bindings[1].resource_type equals `sampler`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reflects WGSL bindings with comments and attribute order variants")
step("reflects WGSL bindings with comments and attribute order variants")
val source = "@fragment fn main() -> @location(0) vec4f { return vec4f(1.0); }\n// @group(0) @binding(9) var ghost: sampler;\n@binding(1) @group(0) var diffuse: texture_2d<f32>;\n  // @group(0) @binding(8) var shadow: texture_2d<f32>;\n@binding(2) @group(0) var nearest_sampler: sampler;"
val bindings = webgpu_reflect_wgsl_bindings(source)
expect(bindings.len()).to_equal(2)
expect(bindings[0].binding).to_equal(1)
expect(bindings[0].resource_type).to_equal("texture")
expect(bindings[1].binding).to_equal(2)
expect(bindings[1].resource_type).to_equal("sampler")
```

</details>

### pipeline handles

#### creates render and compute pipeline handles

- creates render and compute pipeline handles
- creates render and compute pipeline handles
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is true
   - Expected: rp.id equals `1`
   - Expected: cp.valid is true
   - Expected: cp.id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates render and compute pipeline handles")
step("creates render and compute pipeline handles")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val vs = ctx.create_shader_module("vs", _vertex_wgsl())
val fs = ctx.create_shader_module("fs", _fragment_wgsl())
val cs = ctx.create_shader_module("cs", _compute_wgsl())
val rp = ctx.create_render_pipeline(vs, fs)
val cp = ctx.create_compute_pipeline(cs)
expect(rp.valid).to_equal(true)
expect(rp.id).to_equal(1)
expect(cp.valid).to_equal(true)
expect(cp.id).to_equal(2)
```

</details>

#### validates render pipeline layouts against reflected shader bindings

- validates render pipeline layouts against reflected shader bindings
- validates render pipeline layouts against reflected shader bindings
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is true
   - Expected: rp.id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("validates render pipeline layouts against reflected shader bindings")
step("validates render pipeline layouts against reflected shader bindings")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var resources = ctx.resources
val layout = resources.create_bind_group_layout("material", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.texture(1, WEBGPU_SHADER_STAGE_FRAGMENT),
    GPUBindGroupLayoutEntry.sampler(2, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_bindings())
val rp = ctx.create_render_pipeline_with_layouts(vs, fs, [layout])
expect(rp.valid).to_equal(true)
expect(rp.id).to_equal(1)
```

</details>

#### derives render pipeline layout from WGSL bindings

- derives render pipeline layout from WGSL bindings
- derives render pipeline layout from WGSL bindings
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is true
   - Expected: rp.id equals `1`
   - Expected: ctx.resources.bind_group_layouts.len() equals `1`
   - Expected: layout.entries.len() equals `3`
   - Expected: layout.entries[0].binding equals `0`
   - Expected: layout.entries[0].visibility equals `WEBGPU_SHADER_STAGE_VERTEX`
   - Expected: layout.entries[0].binding_type equals `WEBGPU_BINDING_TYPE_UNIFORM_BUFFER`
   - Expected: layout.entries[1].binding_type equals `WEBGPU_BINDING_TYPE_TEXTURE`
   - Expected: layout.entries[2].binding_type equals `WEBGPU_BINDING_TYPE_SAMPLER`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("derives render pipeline layout from WGSL bindings")
step("derives render pipeline layout from WGSL bindings")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_bindings())
val rp = ctx.create_render_pipeline_auto_layout(vs, fs)
expect(rp.valid).to_equal(true)
expect(rp.id).to_equal(1)
expect(ctx.resources.bind_group_layouts.len()).to_equal(1)
val layout = ctx.resources.bind_group_layouts[0]
expect(layout.entries.len()).to_equal(3)
expect(layout.entries[0].binding).to_equal(0)
expect(layout.entries[0].visibility).to_equal(WEBGPU_SHADER_STAGE_VERTEX)
expect(layout.entries[0].binding_type).to_equal(WEBGPU_BINDING_TYPE_UNIFORM_BUFFER)
expect(layout.entries[1].binding_type).to_equal(WEBGPU_BINDING_TYPE_TEXTURE)
expect(layout.entries[2].binding_type).to_equal(WEBGPU_BINDING_TYPE_SAMPLER)
```

</details>

#### merges automatic layout visibility for shared shader bindings

- merges automatic layout visibility for shared shader bindings
- merges automatic layout visibility for shared shader bindings
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is true
   - Expected: layout.entries.len() equals `1`
   - Expected: layout.entries[0].binding equals `0`
   - Expected: layout.entries[0].visibility equals `WEBGPU_SHADER_STAGE_VERTEX | WEBGPU_SHADER_STAGE_FRAGMENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("merges automatic layout visibility for shared shader bindings")
step("merges automatic layout visibility for shared shader bindings")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_shared_uniform())
val rp = ctx.create_render_pipeline_auto_layout(vs, fs)
expect(rp.valid).to_equal(true)
val layout = ctx.resources.bind_group_layouts[0]
expect(layout.entries.len()).to_equal(1)
expect(layout.entries[0].binding).to_equal(0)
expect(layout.entries[0].visibility).to_equal(WEBGPU_SHADER_STAGE_VERTEX | WEBGPU_SHADER_STAGE_FRAGMENT)
```

</details>

#### rejects automatic render layouts with sparse bind groups

- rejects automatic render layouts with sparse bind groups
- rejects automatic render layouts with sparse bind groups
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is false
   - Expected: rp.error equals `GPURenderPipeline auto layout requires contiguous bind groups`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects automatic render layouts with sparse bind groups")
step("rejects automatic render layouts with sparse bind groups")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_sparse_group())
val rp = ctx.create_render_pipeline_auto_layout(vs, fs)
expect(rp.valid).to_equal(false)
expect(rp.error).to_equal("GPURenderPipeline auto layout requires contiguous bind groups")
```

</details>

#### rejects automatic render layouts with incompatible shared bindings

- rejects automatic render layouts with incompatible shared bindings
- rejects automatic render layouts with incompatible shared bindings
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is false
   - Expected: rp.error equals `GPURenderPipeline layout binding type does not match shader resource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects automatic render layouts with incompatible shared bindings")
step("rejects automatic render layouts with incompatible shared bindings")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_conflicting_binding())
val rp = ctx.create_render_pipeline_auto_layout(vs, fs)
expect(rp.valid).to_equal(false)
expect(rp.error).to_equal("GPURenderPipeline layout binding type does not match shader resource")
```

</details>

#### derives automatic layouts for storage resources

- derives automatic layouts for storage resources
- derives automatic layouts for storage resources
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is true
   - Expected: layout.entries[1].binding_type equals `WEBGPU_BINDING_TYPE_STORAGE_BUFFER`
   - Expected: layout.entries[2].binding_type equals `WEBGPU_BINDING_TYPE_STORAGE_TEXTURE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("derives automatic layouts for storage resources")
step("derives automatic layouts for storage resources")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_storage_bindings())
val rp = ctx.create_render_pipeline_auto_layout(vs, fs)
expect(rp.valid).to_equal(true)
val layout = ctx.resources.bind_group_layouts[0]
expect(layout.entries[1].binding_type).to_equal(WEBGPU_BINDING_TYPE_STORAGE_BUFFER)
expect(layout.entries[2].binding_type).to_equal(WEBGPU_BINDING_TYPE_STORAGE_TEXTURE)
```

</details>

#### rejects automatic layouts with unsupported reflected resources

- rejects automatic layouts with unsupported reflected resources
- rejects automatic layouts with unsupported reflected resources
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is false
   - Expected: rp.error equals `GPURenderPipeline auto layout binding type is not supported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects automatic layouts with unsupported reflected resources")
step("rejects automatic layouts with unsupported reflected resources")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_unknown_binding())
val rp = ctx.create_render_pipeline_auto_layout(vs, fs)
expect(rp.valid).to_equal(false)
expect(rp.error).to_equal("GPURenderPipeline auto layout binding type is not supported")
```

</details>

#### rejects render pipeline layouts that miss reflected shader resources

- rejects render pipeline layouts that miss reflected shader resources
- rejects render pipeline layouts that miss reflected shader resources
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: missing_pipeline.valid is false
   - Expected: missing_pipeline.error equals `GPURenderPipeline layout missing shader binding`
   - Expected: visibility_pipeline.error equals `GPURenderPipeline layout visibility does not include shader stage`
   - Expected: type_pipeline.error equals `GPURenderPipeline layout binding type does not match shader resource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects render pipeline layouts that miss reflected shader resources")
step("rejects render pipeline layouts that miss reflected shader resources")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var resources = ctx.resources
val missing = resources.create_bind_group_layout("missing", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.texture(1, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val wrong_visibility = resources.create_bind_group_layout("visibility", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_FRAGMENT),
    GPUBindGroupLayoutEntry.texture(1, WEBGPU_SHADER_STAGE_FRAGMENT),
    GPUBindGroupLayoutEntry.sampler(2, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val wrong_type = resources.create_bind_group_layout("wrong-type", [
    GPUBindGroupLayoutEntry.buffer(0, WEBGPU_SHADER_STAGE_VERTEX),
    GPUBindGroupLayoutEntry.sampler(1, WEBGPU_SHADER_STAGE_FRAGMENT),
    GPUBindGroupLayoutEntry.sampler(2, WEBGPU_SHADER_STAGE_FRAGMENT)
])
val vs = ctx.create_shader_module("vs", _vertex_wgsl_with_bindings())
val fs = ctx.create_shader_module("fs", _fragment_wgsl_with_bindings())
val missing_pipeline = ctx.create_render_pipeline_with_layouts(vs, fs, [missing])
expect(missing_pipeline.valid).to_equal(false)
expect(missing_pipeline.error).to_equal("GPURenderPipeline layout missing shader binding")
val visibility_pipeline = ctx.create_render_pipeline_with_layouts(vs, fs, [wrong_visibility])
expect(visibility_pipeline.error).to_equal("GPURenderPipeline layout visibility does not include shader stage")
val type_pipeline = ctx.create_render_pipeline_with_layouts(vs, fs, [wrong_type])
expect(type_pipeline.error).to_equal("GPURenderPipeline layout binding type does not match shader resource")
```

</details>

#### rejects render pipeline with compute shader in vertex slot

- rejects render pipeline with compute shader in vertex slot
- rejects render pipeline with compute shader in vertex slot
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: rp.valid is false
   - Expected: rp.error equals `valid vertex shader required`
   - Expected: ctx.last_error equals `valid vertex shader required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects render pipeline with compute shader in vertex slot")
step("rejects render pipeline with compute shader in vertex slot")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val cs = ctx.create_shader_module("cs", _compute_wgsl())
val fs = ctx.create_shader_module("fs", _fragment_wgsl())
val rp = ctx.create_render_pipeline(cs, fs)
expect(rp.valid).to_equal(false)
expect(rp.error).to_equal("valid vertex shader required")
expect(ctx.last_error).to_equal("valid vertex shader required")
```

</details>

#### rejects shader and pipeline creation before device readiness

- rejects shader and pipeline creation before device readiness
- rejects shader and pipeline creation before device readiness
   - Expected: module.valid is false
   - Expected: module.error equals `device is not ready`
   - Expected: rp.valid is false
   - Expected: rp.error equals `device is not ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects shader and pipeline creation before device readiness")
step("rejects shader and pipeline creation before device readiness")
var ctx = webgpu_create_context(true)
val module = ctx.create_shader_module("vs", _vertex_wgsl())
expect(module.valid).to_equal(false)
expect(module.error).to_equal("device is not ready")
val rp = ctx.create_render_pipeline(module, module)
expect(rp.valid).to_equal(false)
expect(rp.error).to_equal("device is not ready")
```

</details>

#### rejects shader and pipeline creation after device loss

- rejects shader and pipeline creation after device loss
- rejects shader and pipeline creation after device loss
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: lost.lost is true
   - Expected: module.valid is false
   - Expected: module.error equals `device is lost`
   - Expected: rp.valid is false
   - Expected: rp.error equals `device is lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects shader and pipeline creation after device loss")
step("rejects shader and pipeline creation after device loss")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val lost = ctx.lose_device("adapter reset")
expect(lost.lost).to_equal(true)
val module = ctx.create_shader_module("vs", _vertex_wgsl())
expect(module.valid).to_equal(false)
expect(module.error).to_equal("device is lost")
val rp = ctx.create_render_pipeline(module, module)
expect(rp.valid).to_equal(false)
expect(rp.error).to_equal("device is lost")
```

</details>

### device resources

#### creates resources through the device context

- creates resources through the device context
- creates resources through the device context
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: buffer.valid is true
   - Expected: texture.valid is true
   - Expected: sampler.valid is true
   - Expected: layout.valid is true
   - Expected: bind_group.valid is true
   - Expected: ctx.resources.resource_count() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates resources through the device context")
step("creates resources through the device context")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var resources = ctx.resources
val buffer = resources.create_buffer("uniforms", 128, WEBGPU_BUFFER_USAGE_COPY_DST | WEBGPU_BUFFER_USAGE_UNIFORM)
val texture = resources.create_texture("albedo", 32, 32, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST | WEBGPU_TEXTURE_USAGE_TEXTURE_BINDING)
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
ctx.resources = resources
expect(buffer.valid).to_equal(true)
expect(texture.valid).to_equal(true)
expect(sampler.valid).to_equal(true)
expect(layout.valid).to_equal(true)
expect(bind_group.valid).to_equal(true)
expect(ctx.resources.resource_count()).to_equal(5)
```

</details>

#### enforces negotiated resource limits through the context

- enforces negotiated resource limits through the context
- enforces negotiated resource limits through the context
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(descriptor) is true
   - Expected: too_large_buffer.valid is false
   - Expected: too_large_buffer.error equals `GPUBuffer size exceeds device limit`
   - Expected: too_wide_texture.valid is false
   - Expected: too_wide_texture.error equals `GPUTexture width exceeds device limit`
   - Expected: too_deep_2d_array.valid is false
   - Expected: too_deep_2d_array.error equals `GPUTexture depthOrArrayLayers exceeds device limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("enforces negotiated resource limits through the context")
step("enforces negotiated resource limits through the context")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
var limits = GPUDeviceLimits.defaults()
limits.max_buffer_size = 128
limits.max_texture_dimension_2d = 16
limits.max_texture_array_layers = 2
var descriptor = GPUDeviceDescriptor.create()
descriptor.required_limits = limits
expect(ctx.request_device(descriptor)).to_equal(true)

val too_large_buffer = ctx.create_buffer("too-large", 256, WEBGPU_BUFFER_USAGE_COPY_DST)
expect(too_large_buffer.valid).to_equal(false)
expect(too_large_buffer.error).to_equal("GPUBuffer size exceeds device limit")

val too_wide_texture = ctx.create_texture("too-wide", 32, 16, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST)
expect(too_wide_texture.valid).to_equal(false)
expect(too_wide_texture.error).to_equal("GPUTexture width exceeds device limit")

val too_deep_2d_array = ctx.create_texture("too-deep-array", 16, 16, 3, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST)
expect(too_deep_2d_array.valid).to_equal(false)
expect(too_deep_2d_array.error).to_equal("GPUTexture depthOrArrayLayers exceeds device limit")
```

</details>

#### validates dimension-aware 3d texture limits through the context

- validates dimension-aware 3d texture limits through the context
- validates dimension-aware 3d texture limits through the context
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(descriptor) is true
   - Expected: texture.valid is true
   - Expected: too_deep.valid is false
   - Expected: too_deep.error equals `GPUTexture depth exceeds 3d device limit`
   - Expected: mipmapped.valid is true
   - Expected: mipmapped.mip_level_count equals `4`
   - Expected: msaa.valid is true
   - Expected: msaa.sample_count equals `4`
   - Expected: bad_msaa.valid is false
   - Expected: bad_msaa.error equals `GPUTexture multisampled textures must have one mip level`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("validates dimension-aware 3d texture limits through the context")
step("validates dimension-aware 3d texture limits through the context")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
var limits = GPUDeviceLimits.defaults()
limits.max_texture_dimension_3d = 8
var descriptor = GPUDeviceDescriptor.create()
descriptor.required_limits = limits
expect(ctx.request_device(descriptor)).to_equal(true)

val texture = ctx.create_texture_with_dimension("volume", 8, 8, 8, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_3D)
expect(texture.valid).to_equal(true)
val too_deep = ctx.create_texture_with_dimension("too-deep-volume", 8, 8, 9, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_3D)
expect(too_deep.valid).to_equal(false)
expect(too_deep.error).to_equal("GPUTexture depth exceeds 3d device limit")

val mipmapped = ctx.create_texture_with_mip_levels("mip-volume", 8, 8, 4, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_3D, 4)
expect(mipmapped.valid).to_equal(true)
expect(mipmapped.mip_level_count).to_equal(4)

val msaa = ctx.create_texture_with_descriptor("msaa-color", 8, 8, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_2D, 1, 4)
expect(msaa.valid).to_equal(true)
expect(msaa.sample_count).to_equal(4)

val bad_msaa = ctx.create_texture_with_descriptor("bad-msaa", 8, 8, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST, WEBGPU_TEXTURE_DIMENSION_2D, 2, 4)
expect(bad_msaa.valid).to_equal(false)
expect(bad_msaa.error).to_equal("GPUTexture multisampled textures must have one mip level")
```

</details>

#### rejects resource creation before device readiness

- rejects resource creation before device readiness
- rejects resource creation before device readiness
   - Expected: ctx.queue_write_buffer(1, 0, 8) is false
   - Expected: ctx.last_error equals `device is not ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects resource creation before device readiness")
step("rejects resource creation before device readiness")
var ctx = webgpu_create_context(true)
expect(ctx.queue_write_buffer(1, 0, 8)).to_equal(false)
expect(ctx.last_error).to_equal("device is not ready")
```

</details>

### device command and status surface

#### creates command encoder and submits through the context queue

- creates command encoder and submits through the context queue
- creates command encoder and submits through the context queue
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: encoder.begin_render_pass() is true
   - Expected: encoder.draw(3, 1) is true
   - Expected: encoder.end_render_pass() is true
   - Expected: command_buffer.valid is true
   - Expected: ctx.queue_submit([command_buffer]) is true
   - Expected: ctx.queue.submitted_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates command encoder and submits through the context queue")
step("creates command encoder and submits through the context queue")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var encoder = ctx.create_command_encoder("frame")
expect(encoder.begin_render_pass()).to_equal(true)
expect(encoder.draw(3, 1)).to_equal(true)
expect(encoder.end_render_pass()).to_equal(true)
val command_buffer = encoder.finish("frame-commands")
expect(command_buffer.valid).to_equal(true)
expect(ctx.queue_submit([command_buffer])).to_equal(true)
expect(ctx.queue.submitted_count()).to_equal(1)
```

</details>

#### routes queue writes through the context queue

- routes queue writes through the context queue
- routes queue writes through the context queue
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.queue_write_buffer(buffer.id, 0, 32) is true
   - Expected: queue.write_texture(texture.id, 4, 4, 1, 64) is true
   - Expected: ctx.queue.write_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("routes queue writes through the context queue")
step("routes queue writes through the context queue")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var resources = ctx.resources
val buffer = resources.create_buffer("upload", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
val texture = resources.create_texture("upload-texture", 4, 4, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST)
ctx.resources = resources
expect(ctx.queue_write_buffer(buffer.id, 0, 32)).to_equal(true)
var queue = ctx.queue
expect(queue.write_texture(texture.id, 4, 4, 1, 64)).to_equal(true)
ctx.queue = queue
expect(ctx.queue.write_count()).to_equal(2)
```

</details>

#### executes context-submitted compute commands with uploaded buffer state

- executes context-submitted compute commands with uploaded buffer state
- executes context-submitted compute commands with uploaded buffer state
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.queue_write_buffer(buffer.id, 0, 32) is true
   - Expected: encoder.begin_compute_pass() is true
   - Expected: encoder.set_pipeline(cp.id) is true
   - Expected: encoder.dispatch_workgroups(4, 1, 1) is true
   - Expected: encoder.end_compute_pass() is true
   - Expected: ctx.queue_submit([command_buffer]) is true
   - Expected: result.valid is true
   - Expected: result.queue_write_count equals `1`
   - Expected: result.queue_write_bytes equals `32`
   - Expected: result.buffer_state_count equals `1`
   - Expected: result.buffer_checksum equals `33`
   - Expected: result.compute_pass_count equals `1`
   - Expected: result.dispatch_count equals `1`
   - Expected: result.dispatched_workgroups equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("executes context-submitted compute commands with uploaded buffer state")
step("executes context-submitted compute commands with uploaded buffer state")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var resources = ctx.resources
val buffer = resources.create_buffer("storage", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
ctx.resources = resources
val cs = ctx.create_shader_module("cs", _compute_wgsl())
val cp = ctx.create_compute_pipeline(cs)
expect(ctx.queue_write_buffer(buffer.id, 0, 32)).to_equal(true)
var encoder = ctx.create_command_encoder("compute")
expect(encoder.begin_compute_pass()).to_equal(true)
expect(encoder.set_pipeline(cp.id)).to_equal(true)
expect(encoder.dispatch_workgroups(4, 1, 1)).to_equal(true)
expect(encoder.end_compute_pass()).to_equal(true)
val command_buffer = encoder.finish("compute-commands")
expect(ctx.queue_submit([command_buffer])).to_equal(true)
val result = webgpu_software_execute_queue(ctx.queue)
expect(result.valid).to_equal(true)
expect(result.queue_write_count).to_equal(1)
expect(result.queue_write_bytes).to_equal(32)
expect(result.buffer_state_count).to_equal(1)
expect(result.buffer_checksum).to_equal(33)
expect(result.compute_pass_count).to_equal(1)
expect(result.dispatch_count).to_equal(1)
expect(result.dispatched_workgroups).to_equal(4)
```

</details>

#### routes context texture uploads into software executor texture state

- routes context texture uploads into software executor texture state
- routes context texture uploads into software executor texture state
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: queue.write_texture(texture.id, 4, 4, 1, 64) is true
   - Expected: ctx.queue.write_count() equals `1`
   - Expected: result.valid is true
   - Expected: result.queue_write_count equals `1`
   - Expected: result.queue_write_bytes equals `64`
   - Expected: result.texture_state_count equals `1`
   - Expected: result.texture_checksum equals `81`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("routes context texture uploads into software executor texture state")
step("routes context texture uploads into software executor texture state")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var resources = ctx.resources
val texture = resources.create_texture("upload-texture", 4, 4, 1, GPU_TEXTURE_FORMAT_RGBA8_UNORM, WEBGPU_TEXTURE_USAGE_COPY_DST)
ctx.resources = resources
var queue = ctx.queue
expect(queue.write_texture(texture.id, 4, 4, 1, 64)).to_equal(true)
ctx.queue = queue
expect(ctx.queue.write_count()).to_equal(1)
val result = webgpu_software_execute_queue(ctx.queue)
expect(result.valid).to_equal(true)
expect(result.queue_write_count).to_equal(1)
expect(result.queue_write_bytes).to_equal(64)
expect(result.texture_state_count).to_equal(1)
expect(result.texture_checksum).to_equal(81)
```

</details>

#### rejects queue writes that do not match device resources

- rejects queue writes that do not match device resources
- rejects queue writes that do not match device resources
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.queue_write_buffer(buffer.id, 0, 8) is false
   - Expected: ctx.last_error equals `GPUQueue writeBuffer buffer missing COPY_DST usage`
   - Expected: ctx.queue_write_buffer(99, 0, 8) is false
   - Expected: ctx.last_error equals `GPUQueue writeBuffer buffer does not exist`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects queue writes that do not match device resources")
step("rejects queue writes that do not match device resources")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
var resources = ctx.resources
val buffer = resources.create_buffer("uniform", 16, WEBGPU_BUFFER_USAGE_UNIFORM)
ctx.resources = resources
expect(ctx.queue_write_buffer(buffer.id, 0, 8)).to_equal(false)
expect(ctx.last_error).to_equal("GPUQueue writeBuffer buffer missing COPY_DST usage")
expect(ctx.queue_write_buffer(99, 0, 8)).to_equal(false)
expect(ctx.last_error).to_equal("GPUQueue writeBuffer buffer does not exist")
```

</details>

#### captures validation errors through context error scopes

- captures validation errors through context error scopes
- captures validation errors through context error scopes
   - Expected: ctx.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: ctx.report_validation_error("bad command buffer") is true
   - Expected: err.captured is true
   - Expected: err.message equals `bad command buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("captures validation errors through context error scopes")
step("captures validation errors through context error scopes")
var ctx = webgpu_create_context(true)
expect(ctx.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(true)
expect(ctx.report_validation_error("bad command buffer")).to_equal(true)
val err = ctx.pop_error_scope()
expect(err.captured).to_equal(true)
expect(err.message).to_equal("bad command buffer")
```

</details>

#### marks command creation unavailable after device loss

- marks command creation unavailable after device loss
- marks command creation unavailable after device loss
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: lost.lost is true
   - Expected: webgpu_is_available(ctx) is false
   - Expected: webgpu_adapter_status(ctx) equals `unavailable: device lost`
   - Expected: encoder.finished is true
   - Expected: encoder.last_error equals `device is lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("marks command creation unavailable after device loss")
step("marks command creation unavailable after device loss")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
val lost = ctx.lose_device("adapter reset")
expect(lost.lost).to_equal(true)
expect(webgpu_is_available(ctx)).to_equal(false)
expect(webgpu_adapter_status(ctx)).to_equal("unavailable: device lost")
val encoder = ctx.create_command_encoder("after-loss")
expect(encoder.finished).to_equal(true)
expect(encoder.last_error).to_equal("device is lost")
```

</details>

#### destroys the device and clears queued resource state

- destroys the device and clears queued resource state
- destroys the device and clears queued resource state
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.configure_canvas(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480) is true
   - Expected: buffer.valid is true
   - Expected: ctx.queue_write_buffer(buffer.id, 0, 32) is true
   - Expected: ctx.resources.resource_count() equals `1`
   - Expected: ctx.queue.write_count() equals `1`
   - Expected: lost.lost is true
   - Expected: lost.reason equals `WEBGPU_DEVICE_LOST_REASON_DESTROYED`
   - Expected: ctx.device_ready is false
   - Expected: ctx.device_lost is true
   - Expected: ctx.canvas_configured is false
   - Expected: ctx.resources.resource_count() equals `0`
   - Expected: ctx.resources.next_resource_id equals `1`
   - Expected: ctx.queue.write_count() equals `0`
   - Expected: ctx.queue_submit([]) is false
   - Expected: ctx.last_error equals `device is lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("destroys the device and clears queued resource state")
step("destroys the device and clears queued resource state")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
expect(ctx.configure_canvas(GPU_TEXTURE_FORMAT_BGRA8_UNORM, 640, 480)).to_equal(true)
val buffer = ctx.create_buffer("upload", 64, WEBGPU_BUFFER_USAGE_COPY_DST)
expect(buffer.valid).to_equal(true)
expect(ctx.queue_write_buffer(buffer.id, 0, 32)).to_equal(true)
expect(ctx.resources.resource_count()).to_equal(1)
expect(ctx.queue.write_count()).to_equal(1)
val lost = ctx.destroy()
expect(lost.lost).to_equal(true)
expect(lost.reason).to_equal(WEBGPU_DEVICE_LOST_REASON_DESTROYED)
expect(ctx.device_ready).to_equal(false)
expect(ctx.device_lost).to_equal(true)
expect(ctx.canvas_configured).to_equal(false)
expect(ctx.resources.resource_count()).to_equal(0)
expect(ctx.resources.next_resource_id).to_equal(1)
expect(ctx.queue.write_count()).to_equal(0)
expect(ctx.queue_submit([])).to_equal(false)
expect(ctx.last_error).to_equal("device is lost")
```

</details>

#### rejects context error-scope operations after device loss

- rejects context error-scope operations after device loss
- rejects context error-scope operations after device loss
   - Expected: ctx.request_adapter(GPURequestAdapterOptions.default_options()) is true
   - Expected: ctx.request_device(GPUDeviceDescriptor.create()) is true
   - Expected: ctx.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is true
   - Expected: lost.lost is true
   - Expected: ctx.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION) is false
   - Expected: ctx.report_validation_error("late validation") is false
   - Expected: err.captured is false
   - Expected: ctx.last_error equals `device is lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects context error-scope operations after device loss")
step("rejects context error-scope operations after device loss")
var ctx = webgpu_create_context(true)
expect(ctx.request_adapter(GPURequestAdapterOptions.default_options())).to_equal(true)
expect(ctx.request_device(GPUDeviceDescriptor.create())).to_equal(true)
expect(ctx.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(true)
val lost = ctx.lose_device("adapter reset")
expect(lost.lost).to_equal(true)
expect(ctx.push_error_scope(WEBGPU_ERROR_FILTER_VALIDATION)).to_equal(false)
expect(ctx.report_validation_error("late validation")).to_equal(false)
val err = ctx.pop_error_scope()
expect(err.captured).to_equal(false)
expect(ctx.last_error).to_equal("device is lost")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 46 |
| Active scenarios | 46 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-WEBGPU-WEBGPU-CONTEXT-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ae17ffb719dddb031689f25d5c45a3ecbf2701a7223ab138c3eeefd55c67255b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae17ffb719dddb031689f25d5c45a3ecbf2701a7223ab138c3eeefd55c67255b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae17ffb719dddb031689f25d5c45a3ecbf2701a7223ab138c3eeefd55c67255b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/web_platform/webgpu/webgpu_context_spec.spl
mirror: doc/06_spec/feature/web_platform/webgpu/webgpu_context_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/webgpu/webgpu_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/webgpu/webgpu_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/webgpu/webgpu_context_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 43 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/webgpu/webgpu_context_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not expose WebGPU in insecure context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgpu/webgpu_context_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requests adapter and device in secure context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/webgpu/webgpu_context_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports fallback compatibility mode when requested' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
