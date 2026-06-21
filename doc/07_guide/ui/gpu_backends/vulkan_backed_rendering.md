# Vulkan-Backed 2D Rendering, Emulation Backends, and GPU Verification

This guide covers the Engine2D Vulkan rendering path, the Metal-on-Vulkan and
DirectX-on-Vulkan emulation backends, and the three reference-oracle harnesses
that verify them (in-suite cross-backend parity, RenderDoc capture, and
Electron/Chromium pixel parity).

## Backends and selection

`Engine2D.create_requested_backend(width, height, name)`
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl`) returns an engine bound to a
single backend, or a CPU fallback. Relevant backend keys:

| key | renders via | notes |
|-----|-------------|-------|
| `vulkan` | `VulkanBackend` (`backend_vulkan.spl`), real `rt_vulkan_*` compute | 9/10 primitives wired (blit pending) |
| `metal` | native `MetalBackend` (macOS); else **Vulkan emulation** → name `metal-on-vulkan` | non-macOS hosts serve the Metal API request through Vulkan |
| `directx-on-vulkan` | `VulkanBackend` (vkd3d/DXVK concept) | additive alias; the legacy `directx` key stays CPU-raster gated by a real vkd3d/Vulkan ICD probe |
| `software` / `cpu` | `SoftwareBackend` | the bit-exact reference oracle |

The emulation backends disclose themselves in `backend_name()`
(`metal-on-vulkan`, `directx-on-vulkan`) rather than claiming a native driver.

## Real Vulkan only runs under the classic interpreter

`rt_vulkan_*` are implemented in the interpreter (`interpreter_extern/gpu.rs`,
`vulkan_dlopen`), which `dlopen`s `libvulkan` and issues real
`vkCreateInstance`/`vkCmdDispatch`. Therefore:

- `bin/simple test` runs specs in the **classic interpreter**, so real Vulkan
  executes there.
- `SIMPLE_EXECUTION_MODE=interpret bin/simple run …` also uses it.
- Default JIT (`bin/simple run`) links the native C stub
  (`runtime_native.c: rt_vulkan_device_count(){return 0;}`) and
  `interpret-optimized` does not register the externs — both report 0 devices.

## SoftwareBackend is the reference oracle

`SoftwareBackend` re-implements each primitive to be **bit-exact** with the GPU
kernels, so cross-backend parity (`pixel_mismatches == 0`) is the verification
contract. `vulkan_compute_oracle_spec.spl` asserts this for clear, rect_filled,
rect_outline, circle_filled, triangle_filled, rounded_rect, circle_outline, and
line (thickness 1) and gradient.

### Fixing a divergent kernel — the `spirv-dis` recipe

The GLSL sources in `backend_vulkan_glsl.spl` can differ from the hand-assembled
SPIR-V blobs. To recover a kernel's real algorithm:

1. Dump the blob to a `.spv` file from Simple via `rt_file_write_bytes`.
2. `build/tools/renderdoc/...`? no — use the system `spirv-dis blob.spv`.
3. Read the integer ops (`OpSDiv`/`OpIMul`/`OpIAdd`) and replicate them exactly
   in `SoftwareBackend`. Simple's integer `/` truncates toward zero, matching
   `OpSDiv`.
4. Verify `pixel_mismatches == 0`, then wire the kernel in `backend_vulkan.spl`.

This is how `line` (divisor is `steps+1`, not `steps`) and `gradient` (integer,
divisor `rh` not `rh-1`) were fixed. Known remaining: `blit` needs a two-buffer
descriptor layout; the `line` blob ignores thickness (1px only).

## Verification harnesses

### Cross-backend parity (in test suite)
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
  — Engine2D Vulkan / Metal-on-Vulkan / DirectX-on-Vulkan vs Software.
- `test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl`
  — the web-render API surface through the same three backends. NOTE: to make
  the SSpec runner exercise real GPU, the spec creates `VulkanBackend` directly
  in a prior `it` (priming `rt_vulkan_*`), then uses **one** Engine2D-GPU backend
  per `it`, created+drawn **inline** (routing through a helper fn or imported
  module makes the runner fall back to CPU), with a direct `SoftwareBackend`
  reference.

### RenderDoc capture (`scripts/check/check-renderdoc-vulkan-capture.shs`)
A headless compute workload never presents a swapchain frame, so RenderDoc needs
in-application frame markers. The interpreter exposes
`rt_renderdoc_start_capture` / `rt_renderdoc_end_capture` /
`rt_renderdoc_available` / `rt_renderdoc_num_captures`
(`interpreter_extern/gpu.rs`), which fetch the RenderDoc API from the injected
`librenderdoc` and call `StartFrameCapture`/`EndFrameCapture`. Run under
`renderdoccmd capture` (`build/tools/renderdoc`), the harness produces a valid
`.rdc` (validated by its `RDOC` magic). Requires the interpreter binary built
WITH these externs (`src/compiler_rust/target/release/simple`); it does not
replace the self-hosted `bin/release/<triple>/simple`.

### macOS GUI/web/2D Vulkan comparison
The top-level macOS comparison wrapper is
`scripts/setup/setup-gui-web-2d-vulkan-env.shs`. It records host MoltenVK
readiness, direct Electron/Chrome launch evidence, Simple Engine2D Vulkan
readback, and optional RenderDoc captures in
`build/gui-web-2d-vulkan-env/evidence.env`:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
SIMPLE_BIN=src/compiler_rust/target/release/simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

On macOS, `vulkaninfo --summary` reporting `driverName = MoltenVK` proves only
the host Vulkan loader path. It does not prove that Electron or Chrome accepted
ANGLE Vulkan, and it does not install RenderDoc. If Chromium logs reject
`angle=vulkan`, record `vulkan-angle-unavailable` and keep the browser Vulkan
gate failed. If `renderdoccmd` is missing, the setup evidence records
`gui_web_2d_vulkan_renderdoc_reason` and the searched RenderDoc paths; install
`RenderDoc.app` manually or set `RDOC_HOME` before claiming `.rdc` evidence.
Windows and Linux should reuse these same evidence keys when their capture
runbooks are added.

### Electron / Chromium parity (`scripts/check/check-electron-vulkan-web-parity.shs`)
Renders a page through real Chromium (Electron + `xvfb`, via
`tools/electron-live-bitmap/capture_html_argb.js`) and through the Vulkan-backed
Engine2D web surface, then asserts the frames are pixel-identical. Chromium is
the reference oracle. Requires `tools/electron-shell/node_modules` + `xvfb-run`;
skips cleanly otherwise.

## Known gaps
- `blit` Vulkan kernel (two-buffer descriptor layout) — not yet wired.
- `line` GPU kernel is 1px-only (thickness not implemented in the blob).
- The web-render path's GPU provenance fix (legacy `simple_web_*` stamp) remains
  diagnosed but unconverted; the new `web_render_html_via_engine2d` is the
  honest path.
- Related bug docs: `doc/08_tracking/bug/vulkan_raster_kernels_noop_and_divergent_2026-06-17.md`,
  `web_render_gpu_backend_provenance_fabricated_2026-06-17.md`,
  `rt_vulkan_only_executes_under_classic_interpret_2026-06-17.md`.
