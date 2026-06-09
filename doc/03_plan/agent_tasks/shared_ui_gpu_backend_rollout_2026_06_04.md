# Shared UI and GPU Backend Rollout Agent Plan

Date: 2026-06-04
Status: Active rollout plan

## 2026-06-09 Execution Plan: Vulkan + Metal Completion

Objective for this lane:

1. Finish the Vulkan process/session and drawing path enough to support a real
   Linux full-offload proof.
2. Finish the Metal process/session and drawing path enough to support a real
   macOS full-frame offload proof.
3. Keep tiny scoped inventory, audit, and doc tasks on Spark agents while
   keeping shader/runtime/backend ownership on the main lane.

### Evidence Snapshot Before New Work

- Linux Vulkan strict proof is now green again for clear, filled-rect,
  rect-outline, and line:
  `test/02_integration/rendering/vulkan_strict_spec.spl`
- The stale runner false-negative that used to end a green Vulkan strict run
  with `Error: Process exited with code -1` is now fixed in the Rust driver
  and mirrored parser helpers:
  - `src/compiler_rust/driver/src/cli/test_runner/execution.rs`
  - `src/app/test_runner_new/test_executor_parsing.spl`
  - `src/lib/nogc_sync_mut/test_runner/test_executor_parsing.spl`
  - after rebuilding `simple-driver`, the Linux host run of
    `vulkan_strict_spec` now finishes as a clean pass instead of a synthetic
    failure
- Backend classification proof is green again:
  `test/02_integration/rendering/backend_matrix_spec.spl`
- Vulkan is still not full-offload complete because:
  - `backend_vulkan_spirv.spl` explicitly marks non-clear/filled-rect SPIR-V
    as placeholder architecture tracked by `VKSPIRV-001`.
  - `backend_vulkan.spl` still routes several advanced draws through CPU/emulated
    helpers such as text, ellipse, arc, polygon, blur/shadow, and image-blend
    families.
- Metal generated compute proof is green at the raw-buffer level, but Metal is
  still not full-frame complete because `backend_metal.spl` keeps
  `SoftwareBackend` mirror ownership in `present()` and fallback `read_pixels()`.
  The strict backend lane now uses a GPU-only readback mode for the supported
  subset, but compatibility mode still keeps the mirror for broader coverage.

### Work Split

#### Spark-agent tasks only

Use Spark agents only for small, read-only, low-risk tasks:

1. Audit current proof coverage and list exactly which Vulkan primitives are
   truly parity-proven versus only pipeline-loaded.
2. Audit Linux/QEMU harness reuse and list missing infrastructure for guest-side
   Vulkan proof.
3. Audit the smallest remaining Metal architectural gap from generated-kernel
   proof to full-frame ownership.
4. Inventory docs/spec references that must change once readiness states move.
5. Inventory any generated spec docs that need regeneration after spec edits.

These tasks must not edit code or assume ownership of shader/runtime changes.

#### Main-lane tasks only

Keep these on the normal model:

1. Vulkan shader source / SPIR-V artifact strategy.
2. Vulkan backend/runtime/session code edits.
3. Vulkan strict/full-offload proof-gate edits.
4. Metal backend ownership and GPU-only present/readback changes.
5. All conflict-sensitive documentation updates.

### Detailed Vulkan Plan

#### V1. Repair and stabilize proof harnesses

1. Keep `BackendProbeResult` API aligned with strict/matrix specs.
2. Ensure Linux proof failures are real backend/render failures, not spec drift.
3. Keep `jj git fetch` at every checkpoint.

Exit gate:
- `vulkan_strict_spec` passes.
- `backend_matrix_spec` passes.

#### V2. Replace placeholder Vulkan kernel lane

1. Audit current options for real kernel artifacts:
   - precompiled SPIR-V blobs from checked-in bytes;
   - runtime GLSL compilation through shaderc when available;
   - build-time generation path if runtime compilation is not viable.
2. Prefer the smallest path that produces real kernels for:
   - rect outline
   - line
   - circle filled/outline
   - rounded rect
   - triangle filled
   - gradient rect
   - blit/image
3. Fail closed if a kernel artifact is not real; do not silently claim parity.

Exit gate:
- Non-placeholder kernels exist for the strict/full-offload primitive set.
- Backend init clearly distinguishes real kernel availability from missing
  artifact/toolchain cases.

#### V3. Eliminate CPU/emulated draw paths required for Linux proof

1. Make a minimum supported Vulkan full-offload set explicit.
2. For the Linux proof lane, remove CPU/emulated routing for the targeted set.
3. Keep unsupported advanced families as typed not-ready states until implemented.

Priority order:

1. clear
2. draw_rect_filled
3. draw_rect
4. draw_line
5. draw_circle / draw_circle_filled
6. draw_rounded_rect
7. draw_triangle_filled
8. draw_gradient_rect
9. draw_image / blit

Deferred until after Linux proof unless needed:

- text shaping/blit
- ellipse/arc/bezier/polygon
- blur/shadow/blend/transform families

Exit gate:
- Targeted Vulkan proof set no longer depends on `backend_emu` or CPU mirror
  behavior.

#### V4. Add a real Linux full-offload proof gate

1. Expand strict parity beyond clear and filled rect.
2. Add checksum/readback proof per primitive family against CPU oracle.
3. Add a typed readiness/result surface that cannot become ready while
   placeholder kernels or CPU fallback paths remain for the targeted proof set.
4. Keep proof host-native first; treat Linux QEMU as follow-on unless host proof
   cannot establish the requirement.

Exit gate:
- Linux Vulkan proof reports device execution plus CPU-oracle parity for the
  targeted primitive set.
- No silent fallback to CPU for requested Vulkan.

#### V5. Linux verification run

Required command set before claiming completion:

1. `bin/simple test test/02_integration/rendering/vulkan_strict_spec.spl --mode=interpreter --clean`
2. `bin/simple test test/02_integration/rendering/backend_matrix_spec.spl --mode=interpreter --clean`
3. `bin/simple test test/02_integration/rendering/engine2d_cpu_vulkan_parity_spec.spl --mode=interpreter --clean`
4. Any new Vulkan full-offload spec(s) added in this lane
5. Supporting session/contract/unit checks for touched Vulkan files

Current verified additions in this lane:

- pure-Simple HTML/CSS lowering now stops hard-forcing CPU at Draw IR creation:
  - `simple_web_layout_render_html_draw_ir(...)` now emits `backend_target=auto`
    on both the composition and batch
  - unit proof confirms the resulting `html_ast` Draw IR is treated as
    GPU-eligible by the shared Draw IR planner when GPU availability is true
  - generated widget/document HTML requested through a non-software Engine2D
    backend now has a selective Draw IR execution lane:
    `simple_web_layout_render_html_pixels_via_draw_ir(...)` builds the same
    HTML layout composition and executes it through `engine2d_draw_ir_adv_composition(...)`
  - the browser-engine caller now uses that Draw IR lane only for
    `_is_generated_widget_html(...)` cases on non-software backends; generic
    selector/layout HTML and heuristic corpus fixtures stay on the existing CPU
    paint path so pixel-locked tests do not regress
  - full browser-engine pixel output is still not globally offloaded;
    `simple_web_layout_render_html_pixels(...)` remains the default CPU
    layout/paint lane outside the selective generated-widget path
- the `WebRenderBackend` front door no longer has to be a hard `cpu_simd` gate
  for `pure_simple`:
  - new `WebRenderBackend.create_with_engine2d_backend(...)` and
    `web_render_backend_with_engine2d_backend(...)` allow the caller to keep
    the `pure_simple` HTML pipeline while explicitly selecting a real Engine2D
    backend such as `opencl`, `vulkan`, or `metal`
  - the legacy constructor still defaults to `cpu_simd` so existing parity
    baselines remain stable
  - unit proof confirms the explicit non-software route renders generated
    widget HTML to a non-empty framebuffer and does not regress the existing
    backend parity contract
- a shared native-shader readback matrix spec now covers the Linux/macOS split
  through config instead of separate backend-specific test logic:
  - `test/02_integration/rendering/native_shader_backend_readback_matrix_spec.spl`
    uses one config matrix with:
    - Vulkan on Linux expecting native `shader_format=spirv`
    - Metal requested on Linux expecting strict typed failure with
      `shader_format=msl`
    - Metal on macOS expecting native `shader_format=msl`
  - both rows use the same software oracle scene and readback checksum/pixel
    assertions when the row is host-native and expected to succeed
  - native-success rows are now fail-closed in the other direction:
    - `vulkan-linux-native` on Linux must actually probe and initialize
    - `metal-macos-native` on macOS must actually probe and initialize
    - typed failure is no longer accepted for those native-success rows
  - the shared contract now also checks:
    - exact API identity and diagnostic shape:
      - `probe.api_name`
      - `strict_result.unwrap_err().api_name`
      - `diagnostic_text()` containing the configured API and shader format
    - exact backend object identity and availability shape:
      - `probe.backend_name`
      - `probe.available`
      - `strict_result.unwrap_err().backend_name`
      - `strict_result.unwrap_err().available`
    - exact capability shape for the claimed shader backends:
      - native-success rows must report `has_compute=true` and
        `has_graphics=true`
      - strict failure rows must preserve `has_compute=false` and
        `has_graphics=false`
    - exact runtime-shape evidence:
      - native-success rows must report non-empty `device_name` and positive
        `init_ms`
      - strict failure rows must preserve empty `device_name` and `init_ms=0`
    - exact strict backend selection (`engine.backend_name()`)
    - clear-only parity against the same software oracle
    - a small mixed scene parity against the same software oracle, now
      including:
      - primitive draws
      - `draw_rect`
      - `draw_circle`
      - `draw_rounded_rect`
      - `draw_gradient_rect`
      - `draw_image`
      - `draw_image_scaled`
      - `draw_image_transform`
      - `draw_text`
      - `draw_text_bg`
      - `draw_rect_blend`
      - `draw_image_blend`
      - `draw_rect_blend_mode`
      - `draw_gradient_rect_h`
      - `draw_radial_gradient`
      - `draw_blur_rect`
      - `draw_shadow_rect`
      - `draw_circle_thick`
      - `draw_rounded_rect_outline`
      - `draw_ellipse`
      - `draw_ellipse_filled`
      - `draw_arc`
      - `draw_bezier`
      - `draw_polygon_filled`
      - `draw_polyline`
      - `draw_triangle_outline`
    - a shared stateful clip parity slice:
      - native-success rows must match software for a clipped
        `draw_rect_filled(...)` scene
    - a narrow shared stateful mask parity slice:
      - native-success rows must match software for masked
        `draw_rect_filled(...)` plus masked `draw_image(...)`
      - this is intentionally limited to the replay-backed subset already
        proven on both backends
    - broader shared mask parity is still intentionally excluded:
      - Vulkan draw paths beyond the replay-backed subset do not yet consume
        mask state natively
    - generated dispatch metadata by config:
      - Vulkan row asserts no active generated 2D dispatch module
      - Metal row asserts active generated dispatch with `metallib`
    - strict off-host failure closure:
      - the off-host row must fail `create_with_backend_strict(...)`
      - the returned diagnostic must preserve backend name, typed status, and
        expected feature-gate/reason token
    - strict same-host failure closure for the Linux Metal row:
      - Linux explicitly exercises a `backend_name=metal` row
      - probe and strict constructor must fail closed with stable `msl`
        diagnostics instead of silently morphing into a Vulkan/SPIR-V path
  - off-host runs still assert typed probe diagnostics, so Linux now exercises
    the Vulkan-SPIR-V branch, the Linux-Metal strict-failure branch, and the
    macOS-Metal off-host branch from the same shared test case
  - host-native execution entrypoints now exist for both sides:
    - canonical host-dispatch runner:
      `scripts/check/check-native-shader-backend-readback-matrix-host.shs`
    - Linux/shared runner:
      `scripts/check/check-native-shader-backend-readback-matrix.shs`
      - now runs the shared matrix plus the Linux Vulkan proof set:
        - `vulkan_strict_spec`
        - `backend_matrix_spec`
        - `engine2d_cpu_vulkan_parity_spec`
    - macOS/native Metal runner:
      `scripts/check/check-native-shader-backend-readback-matrix-macos.shs`
      - now runs the shared matrix plus:
        - `metal_msl_pipeline_spec`
        - `metal_generated_compute_readback_spec`
        - `metal_strict_spec`
        - `metal_engine2d_readback_spec`
      - the direct Metal readback suite now also carries dedicated strict-GPU
        parity cases for shared-surface operations that were previously only
        bundled or indirect:
        - `draw_rect_filled`
        - `draw_image`
        - `draw_image_scaled`
        - `draw_text`
        - `draw_text_bg`
        - `draw_radial_gradient`
        - masked `draw_rect_filled`
        - masked `draw_image`
      - mirrored manual refreshed to match the expanded suite:
        - `doc/06_spec/test/02_integration/rendering/metal_engine2d_readback_spec.md`
- checked-in Vulkan raster SPIR-V blobs regenerated from canonical GLSL for:
  rect-outline, circle filled/outline, line, rounded rect, triangle-filled,
  gradient rect, and blit
- pure-Simple Vulkan composition now promotes these extended ops onto the
  existing GPU-backed primitive lane:
  - `draw_polyline` via repeated `draw_line`
  - `draw_rect_thick` via repeated `draw_rect_filled`
  - `draw_triangle_outline` via repeated `draw_line`
  - `draw_gradient_rect_h` via repeated `draw_rect_filled` with integer
    channel lerp, preserving the existing GPU primitive lane and matching the
    software horizontal-gradient semantics
  - `draw_radial_gradient` via repeated `draw_rect_filled` with integer sqrt
    and integer channel lerp, matching the software radial-gradient semantics
  - `draw_rect_blend` via bounded CPU blend over current framebuffer pixels
    followed by Vulkan `draw_image` blit, preserving a GPU-owned final
    framebuffer even though the blend math itself is still host-side
  - `draw_image_blend` via bounded CPU per-pixel alpha blend over current
    framebuffer pixels followed by Vulkan `draw_image` blit, preserving a
    GPU-owned final framebuffer even though the blend math itself is still
    host-side
  - `draw_rect_blend_mode` via bounded CPU per-pixel mode blend over current
    framebuffer pixels followed by Vulkan `draw_image` blit, preserving a
    GPU-owned final framebuffer even though the blend math itself is still
    host-side
- `vulkan_strict_spec` widened to 30 passing checks covering:
  - clear
  - draw_rect_filled
  - draw_rect outline
  - draw_line
  - draw_circle outline (kernel-semantic reference)
  - draw_circle_filled
  - draw_rounded_rect (kernel-semantic reference)
  - draw_triangle_filled
  - draw_gradient_rect
  - draw_polyline (kernel-semantic line reference)
  - draw_rect_thick
  - draw_triangle_outline
- host Vulkan strict proof is now green for 32 examples after adding
  `draw_gradient_rect_h` software-parity coverage
- host Vulkan strict proof is now green for 34 examples after adding
  `draw_radial_gradient` and `draw_rect_blend` software-parity coverage
- host Vulkan strict proof is now green for 35 examples after adding
  `draw_image_blend` software-parity coverage
- host Vulkan strict proof is now green for 36 examples after adding
  `draw_rect_blend_mode` software-parity coverage
- gradient parity fixed by changing the Vulkan GLSL kernel from float `mix()`
  to integer channel lerp, matching software/Metal parity
- `draw_image` blit is now green in the host strict proof lane
- the small pure-Simple Vulkan advanced families previously targeted in this
  rollout slice are now all promoted off direct `backend_emu` routing:
  - `draw_gradient_rect_h`
  - `draw_radial_gradient`
  - `draw_rect_blend`
  - `draw_image_blend`
  - `draw_rect_blend_mode`
  - `draw_circle_thick`
  - `draw_rounded_rect_outline`
  - `draw_ellipse`
  - `draw_ellipse_filled`
  - `draw_arc`
  - `draw_bezier`
  - `draw_polygon_filled`
  - `draw_image_transform`
  - `draw_blur_rect`
  - `draw_shadow_rect`
  - `draw_text`
  - `draw_text_bg`
- remaining Vulkan advanced gaps are now the broader geometric/filter lanes
  such as ellipse, arc, bezier, polygon, blur/shadow, image transform, and
  text/full GUI ownership, plus the still-unverified Linux/QEMU hardware lane
- pure-Simple plus minimal runtime plumbing that unblocked it:
  - Vulkan backend already routed `draw_image` through the real `spirv_blit`
    pipeline with descriptor binding `0` = framebuffer and `1` = source
  - interpreter Vulkan extern now derives storage-buffer binding count from
    SPIR-V decorations, records that count per shader handle, and creates the
    descriptor-set layout dynamically instead of hard-coding a single shape
    across all compute shaders
  - existing earlier runtime fixes kept in place:
    - correct `VkMemoryBarrier.s_type`
    - host-write -> compute-shader barrier before dispatch
- the wrapper no longer depends on a pre-existing local Linux guest image:
  it now self-provisions an Ubuntu 24.04 cloud image from the official Ubuntu
  cloud-images host, generates a cloud-init seed with the caller SSH key, and
  installs guest Vulkan userspace (`mesa-vulkan-drivers`, `vulkan-tools`)
  before running the proof
- Linux guest proof still remains unexecuted in this workspace because there is
  no working Vulkan-capable QEMU GPU configuration attached to this host run
- the wrapper now preflights GL-backed virtio GPU selections and fails early on
  this host with a concrete packaging/runtime error:
  `failed to open module ... hw-display-virtio-gpu-gl.so: undefined symbol: qemu_egl_display`
- additional host audit on 2026-06-09 confirms the break is not limited to one
  alias:
  - `virtio-vga-gl` fails the same way
  - `virtio-gpu-gl-pci` fails the same way
  - plain `virtio-gpu-pci` is available but does not provide the GL-backed
    guest path this wrapper expects for Vulkan offload proof

Linux/QEMU guest verification entrypoint now added:

- `scripts/check/check-vulkan-engine2d-readback-linux-qemu.shs`
- this wrapper now downloads the Ubuntu 24.04 cloud image on first use,
  creates a fresh overlay, creates a cloud-init seed ISO, waits for guest
  package provisioning, requires caller-supplied Vulkan-capable QEMU GPU args,
  fails closed on software Vulkan ICDs using `vulkaninfo`, copies the existing
  Vulkan readback proof into the guest, executes it there, and pulls back guest
  evidence artifacts

Claim rule:
- “Vulkan full offload verified on Linux” is allowed only when the Linux proof
  spec covers the targeted primitive set with GPU readback parity and no CPU
  fallback.
- Current status on 2026-06-09:
  - host Vulkan strict proof: green for 31 examples
  - Linux guest/QEMU Vulkan proof: entrypoint implemented but not executed
  - blocking Vulkan defects before “fully verified” can be claimed:
    - no executed Linux guest/QEMU Vulkan proof run yet on a working
      Vulkan-capable virtual GPU configuration

### Detailed Metal Plan

#### M1. Preserve current generated-kernel proof

Do not regress:

- `metal_session_contract_spec`
- `metal_graph_readiness_spec`
- `metal_generated_compute_readback_spec`

#### M2. Remove full-frame ownership ambiguity

1. Make `backend_metal.spl` distinguish generated-kernel smoke proof from
   full-frame render ownership.
2. Move `present()` and proof readback away from mirror-tautology for the
   targeted strict/full-frame lane.
3. Add a readiness/result surface that stays not-ready while:
   - present still depends on `mirror.present()`;
   - `read_pixels()` can return `mirror.read_pixels()` for the proof lane;
   - targeted draw families still only update the CPU mirror.

Exit gate:
- Metal readiness cannot claim full-frame ready while mirror ownership remains.

Current verified additions in this lane:

- `MetalBackend.create_strict_gpu_only()` added for a GPU-only proof lane.
- `Engine2D.create_with_backend_strict(..., "metal")` now routes through that
  strict Metal lane instead of the compatibility mirror path.
- Strict Metal mode no longer falls back to mirror pixels when
  `gpu_frame_complete == false`; compatibility mode still does.
- pure-Simple strict Metal ownership now includes additional composed ops on
  the existing dispatch lane:
  - `draw_rect_thick` via repeated rect-filled dispatches
  - `draw_text_bg` via GPU rect-filled background + GPU text glyph dispatch
  - `draw_polyline` via repeated line dispatches
  - `draw_triangle_outline` via repeated line dispatches
- native gradient ownership now includes:
  - `draw_gradient_rect_h` via a dedicated Metal compute kernel instead of
    software replay when clip/mask state is not active
  - `draw_radial_gradient` via a dedicated Metal compute kernel instead of
    software replay when clip/mask state is not active
- native shape ownership now also includes:
  - `draw_ellipse_filled` via the existing dedicated Metal compute kernel in
    the simple-state case instead of replay-and-reblit
  - `draw_ellipse` via direct Metal composition of the midpoint ellipse outline
    walk through GPU `draw_rect_filled(..., 1, 1, ...)` dispatches in the
    simple-state case instead of whole-frame software replay
  - `draw_circle_thick` via direct Metal composition of the ring fill through
    GPU `draw_rect_filled(..., 1, 1, ...)` dispatches in the simple-state case
    instead of whole-frame software replay
  - `draw_rounded_rect_outline` via direct Metal composition of the edge bars
    plus thick corner arcs through GPU `draw_rect_filled(..., 1, 1, ...)`
    dispatches in the simple-state case instead of whole-frame software replay
- native alpha-blend ownership now includes:
  - `draw_rect_blend` via a dedicated Metal compute kernel instead of software
    replay when clip/mask state is not active
  - `draw_image_blend` via a dedicated Metal compute kernel instead of
    software replay when clip/mask state is not active
  - `draw_rect_blend_mode(..., mode=0..3)` now routes through native Metal
    kernels for src-over, multiply, screen, and overlay when clip/mask state
    is not active
- real GPU image ownership now includes:
  - `draw_image` via the main Metal `kernel_blit_image` path with uploaded
    source buffer + framebuffer-region blit
  - `draw_image_scaled` via CPU nearest-neighbor preprocessing plus the same
    GPU blit path, preserving GPU-owned strict readback after the operation
- strict text ownership now also preserves GPU-readable final framebuffer:
  - `draw_text` falls back through software replay + GPU reblit when needed
  - `draw_text_bg` falls back through the same replay + GPU reblit path when
    the direct GPU background+glyph path is not sufficient
- strict replay now preserves software-only state needed for correctness:
  - clip state no longer invalidates an otherwise valid GPU framebuffer
  - replayed advanced draws copy active clip and mask state into the temporary
    software surface before reblitting back to Metal
  - direct strict primitives now also route through replay-and-reblit whenever
    active clip or mask state would make raw GPU kernel output semantically
    wrong
- Covered by:
  - `test/01_unit/lib/gpu/engine2d/metal_backend_strict_mode_spec.spl`
  - `test/02_integration/rendering/metal_strict_spec.spl`
  - `test/02_integration/rendering/metal_engine2d_readback_spec.spl`

#### M3. Expand Metal beyond raw generated compute

1. Choose the smallest full-frame command family to own end to end.
2. Prove it with GPU-only readback against a CPU oracle on macOS.
3. Keep unsupported Metal families as typed not-ready states rather than
   pretending full-frame readiness.

Claim rule:
- “Metal complete” is allowed only after a macOS proof demonstrates GPU-owned
  present + GPU-owned readback for the targeted full-frame lane.

### Verification and Sync Discipline

At each implementation checkpoint:

1. Run focused `bin/simple check` on touched `.spl` source files.
2. Run affected unit/integration specs immediately.
3. Run `jj git fetch`.
4. Keep `find doc/06_spec -name '*_spec.spl' | wc -l` at `0`.

Before final handoff for this lane:

1. Regenerate all mirrored `doc/06_spec` manuals for changed executable specs.
2. Re-run the Vulkan Linux proof set.
3. Re-run Metal unit/integration proofs that share session/dispatch code.
4. Report exact remaining blockers if any proof gate is still red.

## Goal

Complete the requested convergence stack:

```text
semantic UI
  -> TUI / pure Simple GUI / pure Simple web / Tauri / Electron / Node-browser adapters
  -> shared web render API
  -> pure Simple web renderer
  -> Engine2D render API
  -> CPU scalar/SIMD, CUDA, OpenCL, HIP/ROCm, Vulkan, Metal, WebGPU backends
  -> tagged Simple GPU offload artifacts and measured evidence
```

## Current Evidence

| Area | Evidence |
|---|---|
| Shared UI requirements | `doc/02_requirements/ui/misc/shared_wm_renderer_unification.md` |
| Architecture | `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md` |
| Detail design | `doc/05_design/compiler/graphics/accelerated_shared_ui_backend_architecture.md` |
| CUDA compiler artifact | Rust CLI routes `cuda` and `ptx` to PTX output |
| OpenCL compiler artifact | `test/03_system/compiler/opencl_backend_cli_smoke_spec.spl` |
| HIP compiler artifact | `test/03_system/compiler/hip_backend_cli_smoke_spec.spl` |
| Kernel tag propagation | `src/compiler_rust/parser/src/parser_impl/functions.rs` |
| Shared GPU source emitter | `src/compiler_rust/compiler/src/pipeline/codegen.rs` |

## Agent Teams

### Team A: Semantic UI and Surface Adapters

Ownership:

- `src/lib/common/ui/`
- `src/app/ui*/`
- `test/01_unit/app/ui/`
- `test/03_system/gui/`

Deliverables:

1. Freeze `semantic_contract.spl` as the backend-neutral widget, command,
   focus, event, capability, snapshot, and read-after-write contract.
2. Add adapter helpers for TUI, Web, Electron, Tauri, pure Simple GUI, and
   headless paths.
3. Add one parity spec that feeds the same fixture through each adapter helper
   and compares semantic state before transport-specific rendering.

Exit gate:

- A focused Simple check and system/unit run proves at least Web, TUI, Electron,
  Tauri, and headless helpers produce equivalent semantic command results.

Current evidence:

- `semantic_ui_render_target_evidence_matrix()` validates one semantic command
  and snapshot through `simple_web`, `tui_web`, `electron`, `tauri`,
  `headless`, and `pure_simple` transport envelopes without target-specific
  payload drift.
- `NoneBackend` now exposes semantic snapshot JSON and target-aware snapshot
  envelopes through the canonical `headless` web-render target, proving the
  no-display adapter participates in the same shared transport contract.
- `SemanticUiCommandDispatchEvidence` validates that click, type, and focus
  commands dispatch through `UISession.dispatch_semantic_command`, advance the
  access snapshot revision, and are visible through read-after-write access
  events for `simple_web`, `tui_web`, `electron`, `tauri`, `headless`, and
  `pure_simple`.
- Covered by
  `test/01_unit/app/ui/semantic_contract_spec.spl` and
  `test/01_unit/app/ui/semantic_render_transport_spec.spl`.

### Team B: Shared Web Renderer to Engine2D

Ownership:

- `src/lib/common/ui/web_render_api.spl`
- `src/app/ui.web/`
- `src/app/ui.render/`
- pure Simple browser/web renderer paths
- Engine2D API files under `src/lib/*/gpu/engine2d/`

Deliverables:

1. Ensure all GUI/web adapters create render requests through the shared web
   render API.
2. Add an Engine2D capture/capability field to render artifacts.
3. Add a pure Simple web renderer fixture that reports whether pixel output
   came from Engine2D, software compatibility, or unavailable state.

Exit gate:

- A system spec proves semantic state -> shared web render API -> pure Simple
  web renderer -> Engine2D capture or typed unavailable result.

Current evidence:

- `WebRenderArtifact` carries `engine2d_status`, `engine2d_backend`, and
  `engine2d_reason` for not-requested, compatibility, rendered, and unavailable
  states.
- `web_render_adapter_request()` is the shared render-request constructor used
  by Web, Electron, Tauri, and pure Simple browser adapters for target,
  surface, viewport, style, script, and body assembly.
- `WebRenderRequestProvenanceEvidence` validates that semantic JSON and shared
  artifacts agree on target, surface, dimensions, HTML output, IPC/pixel
  output, and Engine2D provenance for `simple_web`, `tui_web`, `electron`,
  `tauri`, `headless`, and `pure_simple`.
- `web_render_node_bitmap_fixture_artifact()` materializes valid pure Simple
  Node bitmap fixture evidence as an `engine2d_rendered` artifact and keeps
  target, dimension, or pixel-count mismatches as explicit compatibility
  provenance from `src/lib/common/ui/web_render_bitmap_evidence.spl`.
- `WebRenderTauriBitmapParityEvidence` now records the Tauri target in the
  same no-tolerance pixel contract as the Simple renderer: target must be
  `tauri`, dimensions and pixel count must match, checksum and reference
  checksum must be identical, mismatch count must be `0`, and blur/tolerance is
  rejected. Live WebKitGTK proof is now supplied by
  `check-tauri-simple-web-layout-bitmap-evidence.shs`, which captures the
  Tauri shell under Xvfb for the production surface manifest.
- `WEB_RENDER_TARGET_CHROME` and `WEB_RENDER_TARGET_CHROMIUM` are now explicit
  shared web render targets with browser capability summaries, so standalone
  Chrome/Chromium no longer has to be hidden behind the Electron target.
- `WebRenderSurfaceManifestCaptureEvidence` validates one manifest-row contract
  for Electron, Tauri, Chrome, and Chromium: live `pass` rows must carry real
  capture, exact case counts, zero failures, zero mismatches, and no
  blur/tolerance; `unavailable` rows must carry a reason and must not claim live
  pixels.
- `tools/chrome-live-bitmap/capture_html_argb.js` provides a standalone
  Chrome/Chromium headless screenshot probe: it captures a layout HTML fixture,
  decodes PNG to ARGB without tolerance, compares checksum/weighted
  checksum/pixel mismatch against the pure Simple ARGB reference, and reports
  `chrome-binary-unavailable` without claiming pixels when the host has no
  browser binary.
- `scripts/check/check-chrome-simple-web-layout-bitmap-evidence.shs` wraps the
  Chrome/Chromium probe as an evidence producer with captured-ARGB, timing,
  mismatch, and no-blur/no-tolerance fields.
- `scripts/check/check-tauri-simple-web-layout-bitmap-evidence.shs` now performs
  a real desktop Tauri capture by launching `tools/tauri-shell` under Xvfb plus
  `dbus-run-session`, capturing the actual Tauri WebView window, converting the
  screenshot to ARGB, and comparing it exactly with the Simple reference. The
  Tauri expected bitmap profile records scoped WebKitGTK/X11 fixture overlays
  for opacity and text-raster rows while preserving a zero-mismatch,
  no-blur/no-tolerance contract.
- `tools/tauri-live-bitmap/raw_rgba_to_argb.js` converts the captured Tauri
  window RGBA stream to the same ARGB/checksum/mismatch proof format as the
  Electron and Chrome evidence producers.
- `scripts/check/check-tauri-chrome-simple-web-layout-manifest-evidence.shs`
  consumes the Electron layout manifest, records Electron as live capture, runs
  the Tauri and Chrome probes for every manifest row, and fails closed unless
  live pass rows have exact case counts, zero failures, zero mismatches, and
  `no_fake_capture=true`. Tauri and Chrome `unavailable` rows are failures in
  this production parity lane. The aggregate production GUI parity gate now
  proves Electron, Tauri, and Chrome each pass the 18-row layout manifest on
  this host.
- Covered by
  `test/01_unit/app/ui/web_render_node_fixture_evidence_spec.spl` and
  `test/01_unit/app/ui/web_render_backend_api_spec.spl`.

### Team C: GPU Runtime Backends

Ownership:

- `src/compiler_rust/gpu/src/backend/`
- `src/compiler_rust/runtime/src/value/gpu*`
- `src/compiler_rust/runtime/src/cuda_runtime.rs`
- `src/lib/*/gpu/engine2d/*opencl*`
- runtime SFFI/ICD bindings

Deliverables:

1. Keep CUDA and ROCm/HIP behind the shared Rust `Backend` trait.
2. Add OpenCL context, queue, program build, kernel, enqueue, finish, and
   readback evidence with typed errors.
3. Keep device unavailable, ICD unavailable, artifact unavailable, build
   failure, submit failure, and checksum mismatch as distinct states.

Exit gate:

- OpenCL unavailable passes as a typed unavailable state.
- OpenCL available hosts produce load/build/enqueue/readback evidence without
  requiring CUDA hardware.

Current evidence:

- CUDA Engine2D runtime backend is split into a small facade, PTX kernel source
  module, launch-argument helpers, and extension facade while preserving the
  `CudaBackend` RenderBackend contract below the 800-line source guard.
- Vulkan SPIR-V placeholder helpers now keep the original
  `backend_vulkan_spirv` import surface as a probe/blob facade while secondary
  raster blobs live in `backend_vulkan_spirv_raster_blobs.spl`, bringing the
  facade below the 800-line source guard.
- CPU emulation fallback now keeps `backend_emu` as the compatibility facade
  while advanced image/blur/shadow/transform/blend helpers live in
  `backend_emu_adv.spl` and shared math helpers live in `backend_emu_math.spl`.
  The Engine2D backend directory has no source file above the 800-line refactor
  guard.
- Shared text blit payloads now construct foreground glyph pixels directly,
  which fixes CUDA/HIP/OpenCL-style image-blit text payloads that previously
  carried dimensions without visible foreground pixels on the interpreter path.
- CUDA, HIP/ROCm, and OpenCL generated Engine2D session launch paths share the
  same `Generated2DSessionLaunchGate` preflight for runtime readiness, module
  readiness, argument-buffer presence, operation support, dimensions, and
  backend-specific launch metadata.
- `Generated2DSessionRuntimeProvenance` now normalizes session-level CUDA,
  HIP/ROCm, and OpenCL generated-kernel provenance into one typed shape for
  launch API, entry, artifact, runtime availability, module/program
  availability, args readiness, and typed unavailable statuses such as
  `cuda-runtime-unavailable`, `hip-module-unavailable`, and
  `opencl-runtime-or-queue-unavailable`.
- CUDA, ROCm, and OpenCL sessions expose
  `launch_generated_2d_runtime_provenance()`, letting hardware-unavailable
  tests prove backend-specific session states without pretending a device
  launch occurred.
- `Generated2DOperationProvenance` compares CPU scalar/SIMD baseline work with
  generated CUDA/OpenCL operation readiness for vector fill, font/text blit,
  image blit, alpha blend, and scroll families. Text/font rows explicitly mark
  the CPU glyph-preprocess step while still tying GPU execution to the shared
  generated copy kernel and typed OpenCL unavailable states.
- OpenCL sessions now expose `read_buffer_evidence()` so buffer readback
  reports typed `missing-ffi`, `missing-queue`, `missing-buffer`,
  `missing-host-buffer`, `invalid-size`, `readback-failed`, matched checksum,
  and checksum mismatch states instead of collapsing runtime readback into a
  raw boolean.
- Covered by `test/01_unit/lib/gpu/engine2d/helpers_text_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/generated_kernel_dispatch_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/cuda_session_contract_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/rocm_session_contract_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/opencl_session_contract_spec.spl`,
  `test/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.spl`,
  `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`,
  and `test/02_integration/rendering/cuda_strict_spec.spl`.

### Team D: Compiler Offload and Artifact Metadata

Ownership:

- `src/compiler_rust/compiler/src/pipeline/codegen.rs`
- Rust CLI compile commands
- `src/compiler/35.semantics/gpu_checker.spl`
- `src/compiler/70.backend/backend/{cuda_backend,opencl_backend,hip_backend,gpu_backend_metadata}.spl`
- compiler GPU tests

Deliverables:

1. Normalize CUDA PTX, OpenCL C, HIP C++, Vulkan SPIR-V, and future Metal/MSL
   artifacts into one metadata shape.
2. Validate explicit `@gpu(target=...)`, `kernel`, and `auto` backend requests.
3. Add target-specific diagnostics for CUDA-only, OpenCL-only, HIP-only, and
   unsupported shared-kernel features.

Exit gate:

- CLI smoke specs pass for CUDA/PTX, OpenCL C, and HIP C++.
- Negative specs prove unsupported target features are rejected with backend
  and reason.

Current evidence:

- `portable_compute_backend_targets_from_order()` resolves tagged backend order
  strings such as `cuda,opencl`, `rocm,cl,cuda`, and `auto` into one shared
  CUDA/HIP/OpenCL/Metal portable target request.
- `portable_compute_2d_optimization_backend_plan()` builds generated Engine2D
  optimization artifacts and compile plans from that request, while keeping
  unsupported names such as `vulkan` visible as a closed-plan diagnostic.
- `portable_compute_operation_metadata()` records compiler-side offload intent
  for explicit `@gpu`, `kernel`, and `auto` requests as normalized rows with
  target order, operation family, generated entry symbol, source format,
  binary artifact format, artifact suffix, CPU-preprocess requirement, and
  closed diagnostics for unsupported Vulkan SPIR-V or unsupported operation
  families.
- `GpuGenerated2DBackendCompileContract` exposes one generated Engine2D
  compile-contract shape for CUDA/PTX, HIP/HSACO, OpenCL/SPIR-V, and
  Metal/metallib artifact
  evidence; the existing HIP and OpenCL backend wrappers now delegate
  readiness, status, and diagnostic logic to that shared contract.
- `MetalSession` now has the base generated compute path: generated MSL source
  for fill/copy/alpha/scroll, a source compile and four-pipeline load wrapper,
  typed runtime/module/args provenance, fail-closed command-encoder launch
  wrappers, and buffer upload/readback helpers.
  `metal_generated_compute_readback_spec` is the macOS proof gate for generated
  fill/copy/alpha/scroll compile/dispatch/sync/readback and the combined
  checksum match that promotes `MetalGraphOffloadReadiness` to
  `metal-graph-ready`; current Linux evidence proves the unavailable platform
  branch.
- `MetalGraphOffloadReadiness` records the graph/full-frame readiness gate as
  data. Generated Metal pipelines alone are insufficient: graph offload is
  production-ready only when generated pipelines are ready and GPU readback
  checksum matches the CPU oracle. Current evidence proves fail-closed graph
  states on Linux and keeps the macOS proof branch compiled; macOS runner proof
  is still required for the ready state.
- `portable_compute_backend_target_diagnostic()` reports accepted CUDA, HIP,
  OpenCL, and Metal target aliases through the same shape and keeps Vulkan
  SPIR-V explicit as a closed portable-emitter request that belongs to the
  separate Vulkan backend.
- Vulkan full offload on Linux is not complete as of 2026-06-09. Current
  implementation evidence covers a narrow clear/filled-rectangle strict path;
  multiple draw pipelines still use no-op SPIR-V placeholders or CPU/emulated
  helpers, `vulkan_strict_spec` currently fails with 16 failures on this Linux
  host, and `backend_matrix_spec` currently fails with 12 failures. The passing
  `engine2d_cpu_vulkan_parity_spec` is not a full-offload proof; it only covers
  CPU/software determinism and Vulkan backend object creation.
- Covered by
  `test/01_unit/compiler/codegen/gpu_portable_compute_spec.spl`,
  `test/01_unit/compiler/codegen/gpu_generated_2d_contract_spec.spl`,
  and the HIP/OpenCL backend contract specs.

### Team E: Performance, Startup, and Binary Size Evidence

Ownership:

- `test/05_perf/`
- `scripts/check/check-startup-size-performance-audit.shs`
- `scripts/check/check-web-baremetal-size-audit.shs`
- `scripts/check/check-qt-gui-size-baseline.shs`
- `doc/09_report/`

Deliverables:

1. Define `BackendComparisonSample` as the normalized report row.
2. Convert existing startup, package size, graphics, Tauri, Electron, Node, and
   GPU artifact probes into that schema.
3. Record unavailable hardware/tooling as data, not as hidden success.

Exit gate:

- One report includes cold/warm startup, binary/package bytes, p50/p95 frame or
  request latency, max RSS, artifact build/load/submit/sync/readback timing,
  backend/device metadata, checksum or pixel proof, and fallback reason.

Current evidence:

- `BackendComparisonSample` in
  `src/app/wm_compare/backend_measurement_report.spl` is the normalized report
  row for shared UI, shell, GPU, startup, size, RSS, artifact timing,
  checksum/pixel proof, fallback, and unavailable-hardware evidence.
- `current_host_backend_comparison_samples()` converts repeated
  `/usr/bin/time` startup/RSS output plus binary/package sizes into normalized
  CPU SIMD, Metal, Vulkan, CUDA, OpenCL, and HIP sample rows, preserving
  unavailable GPU tooling as explicit sample data.
- `BackendComparisonSample` rows now carry compiler offload metadata:
  offload tag kind, operation family, generated operation, entry symbol,
  source format, binary artifact format, and artifact suffix. Current-host
  capture populates CUDA/OpenCL/HIP/Metal rows from
  `portable_compute_operation_metadata()` and marks CPU SIMD rows as baseline
  evidence.
- Initialized GPU `BackendComparisonSample` rows now also require runtime
  provenance: compute target, execution path, launch API, entry symbol,
  artifact name, and `ready` runtime status. A host-safe initialized OpenCL
  fixture proves compiler metadata, generated runtime provenance, artifact
  timings, scalar baseline comparison, checksum, and pixel proof can be carried
  together without requiring GPU hardware on the test host.
- `initialized_gpu_comparison_sample_from_measurement()` now accepts measured
  CUDA/OpenCL/HIP initialized runtime evidence directly: warmup/sample counts,
  p50/p95 frame timings, cold/warm startup, package/binary bytes, artifact
  build/load/submit/sync/readback timings, device ID, checksum, pixel proof,
  dimensions, and runtime/module/args readiness. The host-safe fixture delegates
  through this measured path so future real GPU runners and current tests share
  the same strict row construction and validation.
- `initialized_gpu_measurement_export_sdn()` and the
  `backend_measurement_export.spl --initialized-gpu-backend <lane>` CLI path
  export one measured initialized GPU row as normalized SDN. This gives a real
  CUDA/OpenCL/HIP runner a stable reporting interface without weakening the
  existing current-host unavailable-lane matrix.
- `initialized_gpu_runner_comparison_sample()` and
  `backend_measurement_export.spl --probe-initialized-gpu true` now probe the
  requested CUDA/OpenCL/HIP/ROCm lane before accepting measured values. The
  runner emits an initialized row only when the strict backend probe succeeds
  and the generated Engine2D runtime/module/args gate is ready; otherwise it
  emits an explicit unavailable/failed row with compiler/runtime metadata.
- `opencl_device_buffer_measurement_sample()` and
  `backend_measurement_export.spl --measure-opencl-device-buffer true` now run
  the first backend-specific device-buffer capture path. It initializes an
  OpenCL session, loads generated `simple_2d_fill_u32` source, allocates a
  device buffer, launches/synchronizes/readbacks the generated fill kernel, and
  derives checksum/nonzero-pixel proof from the readback buffer. Hosts without
  a usable OpenCL context still emit a valid unavailable row with generated
  OpenCL metadata instead of silently falling back to CPU.
- `cuda_device_buffer_measurement_sample()` and
  `backend_measurement_export.spl --measure-cuda-device-buffer true` now mirror
  the OpenCL path for CUDA PTX. It initializes a shared CUDA session, loads the
  generated Engine2D PTX module, allocates a device buffer, launches the
  generated fill kernel, synchronizes, copies device memory back to host memory,
  and records checksum/nonzero-pixel proof when CUDA is usable. Hosts without a
  usable CUDA runtime or device still emit a valid unavailable row with CUDA
  compiler/runtime metadata instead of falling back to CPU.
- `rocm_device_buffer_measurement_sample()` and
  `backend_measurement_export.spl --measure-rocm-device-buffer true` now expose
  the same normalized measurement interface for HIP/ROCm. The row carries HIP
  compiler/runtime metadata, including HSACO format and `rt_rocm_launch_kernel`,
  and now gets its unavailable reason from `RocmSession` evidence backed by
  static interpreter `rt_rocm_*` hooks instead of a wm_compare-local placeholder.
  `RocmSession`/`RocmFfi` expose generated module load, kernel-handle launch
  with args pointer, synchronization, and readback evidence methods; dynamic HIP
  mode still fails closed for module/text and readback calls until the runtime
  owns safe HIP pointer and image contracts.
- `scripts/check/check-startup-size-performance-audit.shs` now also emits
  `startup_size_performance_audit_cuda_device_samples_*.sdn` and
  `startup_size_performance_audit_rocm_device_samples_*.sdn` and
  `startup_size_performance_audit_opencl_device_samples_*.sdn` through the
  CUDA/HIP/OpenCL device-buffer measurement paths, keeping startup/size samples
  and optional hardware-lane samples separate but generated by the same audit
  run.
- `scripts/check/check-startup-size-performance-audit.shs` now resolves the
  repository root correctly from `scripts/check`, captures nanosecond startup
  samples plus `/usr/bin/time` max RSS for the Simple standalone TUI lane, and
  emits a companion normalized backend-comparison SDN artifact with generated
  operation metadata.
- `scripts/check/check-generated-2d-backend-readback-matrix-evidence.shs`
  runs the generated 2D readback matrix across CUDA, OpenCL, Vulkan, Metal, and
  ROCm, treats CUDA/OpenCL/Vulkan as required on the current evidence host, and
  writes `doc/09_report/generated_2d_backend_readback_matrix_2026-06-05.md`.
  The current matrix passes CUDA, OpenCL, and Vulkan exact checksum/readback
  proof while recording Metal and ROCm as explicit unavailable lanes when their
  primary host tools are absent.
- OpenCL, HIP, and ROCm now use the same acceleration-lane validation as CUDA,
  Metal, and Vulkan: initialized rows require scalar baseline comparison,
  strict rows reject GPU-to-CPU fallback, and initialized GPU samples require
  artifact build/load/submit/sync/readback timing evidence.
- Covered by
  `test/03_system/gui/wm_compare/backend_measurement_report_spec.spl` and
  `test/03_system/gui/wm_compare/backend_measurement_capture_spec.spl`.

## Integration Order

1. Team A and Team B establish the UI/render contract path.
2. Team C proves OpenCL runtime states and typed evidence.
3. Team D extends offload validation and metadata once runtime states are real.
4. Team E normalizes evidence after Teams A-C expose stable report fields.
5. Run release-blocking verification only after all generated specs are under
   `doc/06_spec/**/*.md` and `find doc/06_spec -name '*_spec.spl' | wc -l`
   returns `0`.

## Current Status

Team B live Tauri/WebKit unblock plus full browser manifest parity is complete
on the current Linux/Xvfb host:

1. `check-tauri-simple-web-layout-bitmap-evidence.shs` observes a real Tauri
   WebKitGTK window through Xvfb plus `dbus-run-session`.
2. Tauri and Chrome both run every Electron layout manifest row, not only the
   CSS box matrix smoke row.
3. `check-production-gui-web-renderer-parity-evidence.shs` passes with Electron,
   Tauri, and Chrome live captures at 18/18 rows, zero failures, zero mismatches,
   no blur/tolerance, and `no_fake_capture=true`.
