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
| `vulkan` | `VulkanBackend` (`backend_vulkan.spl`) through the Vulkan SFFI facades | checked copy/src-over plus nearest-neighbor IMAGE blit wired |
| `metal` | native `MetalBackend` (macOS); else **Vulkan emulation** → name `metal-on-vulkan` | non-macOS hosts serve the Metal API request through Vulkan |
| `directx-on-vulkan` | `VulkanBackend` (vkd3d/DXVK concept) | additive alias; the legacy `directx` key stays CPU-raster gated by a real vkd3d/Vulkan ICD probe |
| `software` / `cpu` | `SoftwareBackend` | the bit-exact reference oracle |

The emulation backends disclose themselves in `backend_name()`
(`metal-on-vulkan`, `directx-on-vulkan`) rather than claiming a native driver.

## Real Vulkan only runs under the classic interpreter

The Vulkan SFFI facade path ultimately reaches interpreter/runtime Vulkan
externs (`interpreter_extern/gpu.rs`, `vulkan_dlopen`), which `dlopen`
`libvulkan` and issue real `vkCreateInstance`/`vkCmdDispatch`. Therefore:

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

1. Dump the blob to a `.spv` file from Simple via the file write-bytes facade.
2. `build/tools/renderdoc/...`? no — use the system `spirv-dis blob.spv`.
3. Read the integer ops (`OpSDiv`/`OpIMul`/`OpIAdd`) and replicate them exactly
   in `SoftwareBackend`. Simple's integer `/` truncates toward zero, matching
   `OpSDiv`.
4. Verify `pixel_mismatches == 0`, then wire the kernel in `backend_vulkan.spl`.

This is how `line` (divisor is `steps+1`, not `steps`) and `gradient` (integer,
divisor `rh` not `rh-1`) were fixed. The shared two-buffer blit now handles
exact copy, src-over, and nearest-neighbor scaled COPY/src-over; the `line` blob still
ignores thickness (1px only).

## Verification harnesses

### Cross-backend parity (in test suite)
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
  — Engine2D Vulkan / Metal-on-Vulkan / DirectX-on-Vulkan vs Software.
- `test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_spec.spl`
  — the web-render API surface through the same three backends. NOTE: to make
  the SSpec runner exercise real GPU, the spec creates `VulkanBackend` directly
  in a prior `it` (priming the Vulkan SFFI facade), then uses **one** Engine2D-GPU backend
  per `it`, created+drawn **inline** (routing through a helper fn or imported
  module makes the runner fall back to CPU), with a direct `SoftwareBackend`
  reference.

### RenderDoc capture (`scripts/check/check-renderdoc-vulkan-capture.shs`)
A headless compute workload never presents a swapchain frame, so RenderDoc needs
in-application frame markers. The harness calls
`app.test.renderdoc_runtime_ops`, whose owner module wraps the RenderDoc
runtime hooks exposed by `interpreter_extern/gpu.rs`. Those hooks fetch the
RenderDoc API from the injected `librenderdoc` and call
`StartFrameCapture`/`EndFrameCapture`. Run under `renderdoccmd capture`
(`build/tools/renderdoc`), the harness produces a valid `.rdc` (validated by
its `RDOC` magic). Requires the interpreter binary built WITH these externs
(`src/compiler_rust/target/release/simple`); it does not replace the
self-hosted `bin/release/<triple>/simple`.

### GUI/web/2D Vulkan comparison
The top-level GUI/web/2D Vulkan comparison wrapper is
`scripts/setup/setup-gui-web-2d-vulkan-env.shs`. It records host Vulkan
readiness, direct Electron/Chrome launch evidence, Simple Engine2D Vulkan
readback, and optional RenderDoc captures in
`build/gui-web-2d-vulkan-env/evidence.env`:

```sh
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

On Linux, current completion evidence is summarized by
`doc/09_report/linux_vulkan_render_log_compare_current_2026-07-02.md` and the
SimpleOS hardening aggregate:
`BUILD_DIR=build/simpleos_hardening_evidence_matrix_current REPORT_PATH=doc/09_report/simpleos_hardening_evidence_matrix_2026-07-03.md sh scripts/check/check-simpleos-hardening-evidence-matrix.shs`.
That aggregate must report `simpleos_hardening_matrix_passed=18/18` and
`simpleos_hardening_gui_renderdoc_vulkan_status=pass` plus
`simpleos_hardening_formal_lean_proofs_status=pass` plus
`simpleos_hardening_formal_riscv_dual_track_status=pass` plus
`simpleos_hardening_formal_critical_concurrency_status=pass` plus
`simpleos_hardening_formal_memory_safety_status=pass` plus
`simpleos_hardening_formal_storage_integrity_status=pass` before claiming the
SimpleOS Vulkan/RenderDoc lane. Windows and macOS still require their
platform-specific runbooks before claiming native platform closure.
The aggregate audit reads setup/readiness evidence from `GUI_WEB_2D_VULKAN_ENV`
and direct runtime comparison evidence from `GUI_WEB_2D_VULKAN_RUN_EVIDENCE_ENV`
when set, otherwise from existing `build/gui-web-2d-vulkan-env-run-*` evidence.
This prevents a readiness-only `--check` env from hiding the latest direct
Electron, Chrome, and Simple comparison result.

On macOS, `vulkaninfo --summary` reporting `driverName = MoltenVK` proves only
the host Vulkan loader path. It does not prove that Electron or Chrome accepted
ANGLE Vulkan, that Simple selected the fresh macOS-capable Rust driver, or that
RenderDoc can capture frames. The macOS setup evidence must also record the
selected Simple driver through
`gui_web_2d_vulkan_simple_bin_selection_reason`, plus
`gui_web_2d_vulkan_renderdoc_macos_homebrew_package_status` and
`gui_web_2d_vulkan_renderdoc_macos_upstream_support_status`; this separates a
valid Simple Vulkan runtime probe and Homebrew Vulkan/MoltenVK install from the
absence of a Homebrew RenderDoc package or official upstream macOS RenderDoc
support. If Chromium logs reject
`angle=vulkan`, record `vulkan-angle-unavailable` and keep the browser Vulkan
gate failed. If `renderdoccmd` is missing, the setup evidence records
`gui_web_2d_vulkan_renderdoc_reason`, package/support status, and the searched
RenderDoc paths; use a project-approved `RenderDoc.app`/fork or set `RDOC_HOME`
to a tree containing `renderdoccmd` before claiming `.rdc` evidence.

Completion requires RenderDoc `.rdc` files whose first bytes are `RDOC` for the
Simple Engine2D lane and for any browser lane being claimed as Vulkan-backed.
Browser bitmap output without ANGLE Vulkan logs and RDOC capture proof remains
fallback comparison evidence.

### Electron / Chromium parity (`scripts/check/check-electron-vulkan-web-parity.shs`)
Renders a page through real Chromium (Electron + `xvfb`, via
`tools/electron-live-bitmap/capture_html_argb.js`) and through the Vulkan-backed
Engine2D web surface, then asserts the frames are pixel-identical. Chromium is
the reference oracle. Requires `tools/electron-shell/node_modules` + `xvfb-run`;
skips cleanly otherwise.

## Known gaps
- `line` GPU kernel is 1px-only (thickness not implemented in the blob).
- The web-render path's GPU provenance fix (legacy `simple_web_*` stamp) remains
  diagnosed but unconverted; the new `web_render_html_via_engine2d` is the
  honest path.
- Related bug docs: `doc/08_tracking/bug/vulkan_raster_kernels_noop_and_divergent_2026-06-17.md`,
  `web_render_gpu_backend_provenance_fabricated_2026-06-17.md`,
  `rt_vulkan_only_executes_under_classic_interpret_2026-06-17.md`.
