<!-- codex-design -->
# Detail Design: WM Glass Theme on Host and SimpleOS

## Data Model

Add common value types in `common.ui.theme_render_snapshot`:

- `ThemeShadowLayer`: x/y offset, blur, spread, RGBA and inset.
- `ThemeMaterialSemantics`: desktop, window, active/inactive title surfaces;
  alpha, blur, saturation, border width/RGBA, radius, ordered shadows,
  typography/text, reduced-transparency solid fallback and contrast.
- `ThemeRenderSnapshot`: ID, family, source reference, source-manifest SHA-256,
  normalized-material SHA-256, composed CSS, semantic colors and material.

The snapshot is immutable by convention. `ResolvedThemePackage` constructs it;
the generated bare-metal module returns the same value. Normalization uses a
fixed field order and integer units (`RGBA8`, pixels, alpha/saturation/contrast
in thousandths) before hashing.

## Theme Package Changes

1. Parse RGBA rather than falling back to opaque hard-coded colors.
2. Parse shape radius/blur/elevation and base typography/material variables.
3. Preserve ordered layered shadows and active/inactive variants.
4. Define/validate missing package variables required by the material contract.
5. Replace `path:length` fingerprinting with sorted path/content SHA-256.
6. Cache by canonical ID and source manifest; expose explicit invalidation only.

## Startup Adapters

`install_resolved_wm_theme(snapshot)` maps the full snapshot into existing WM
theme state. Hosted bootstrap calls it before creating `HostCompositor`.
`gui_entry_desktop.spl` installs `generated_aetheric_dark_theme_snapshot()`
before `DesktopShell` renders its first frame. Both emit the same normalized
identity record.

`WmChromeColors` remains source compatible but gains or composes a material
record; every production consumer reads the installed theme. Default Aqua
values are used only if installation fails and that state is reported as an
unaccepted emergency fallback.

### Persistent hosted runtime and explicit worker handoff (proposed prerequisite)

Add a hosted-only composition type, `HostedThemeRuntime`, constructed exactly
once by the parent branch of `os.hosted.hosted_entry.main()` after runtime heap
availability and before `install_default_host_wm_theme`, winit/backend creation,
`HostCompositor` creation, or `HostedBrowserRendererProcess.start()`. The
worker-argument branch is intentionally excluded: it is a separate process and
receives an already-canonical wire from its parent rather than opening theme
files or owning a transaction store.

The normal host-compositor constructor receives the same explicit runtime
through `HostWmHandle`; direct hosted entry passes it into `_run_hosted_wm`.
There is no lazy/eager module-global mutex and no installer-local store.

```text
HostedThemeRuntime
  store: ThemePackageTransactionStore       # real hosted mutex, one aggregate
  current_install_wire: text                # copied theme_package_install_wire_v1
  current_revision/theme_id/manifest/material: scalar identity
  wm_projection: scalar-only read surface
  gui_projection: scalar-only read surface
  web_projection: scalar-only read surface
```

The store is injected at construction. It exposes `read_wire_copy()` and typed
scalar projection reads, not package/snapshot aggregates, dictionaries, arrays,
locks, or cache handles. Private decoded objects are reconstructed from copied
canonical wire only inside their owner boundary. Source capture is injectable
so one-read-per-canonical-path behavior can be tested.

#### Browser renderer state changes

Extend `HostedBrowserRendererProcess` state from:

```text
new -> starting -> await-init -> active
```

to:

```text
new -> starting -> await-theme-init -> await-init -> active
```

After `ready`, the parent sends `theme_init` containing exactly one bounded
`theme_package_install_wire_v1`. The worker copies and validates the wire,
builds only its process-local snapshot/cache, then replies `theme_ready` with
the scalar `(generation, revision, theme_id, source_manifest_sha256,
material_sha256)`. Only an exact parent-store match transitions to
`await-init`; otherwise the parent closes the worker and exposes no external
Web frame. `init(html)` is therefore the first HTML message but not the first
protocol message.

For a committed later revision, `theme_apply` carries the same canonical wire
and its expected predecessor revision. Worker accepts only the next current
revision, clears revision-keyed CSS/layout/Draw-IR artifact caches, replies
`theme_ready`, and renders a frame tagged with that revision. The parent
accepts that frame only when its active store revision and worker generation
match. On worker crash/restart, parent creates a new generation, repeats
`ready -> theme_init -> theme_ready -> init/replay`, and drops all old
generation frames. The worker never reads the package filesystem.

#### Commit, application, and notification sequence

`HostedThemeRuntime.refresh(expected_revision, source_reader)` has this
algorithm:

1. capture registry and every referenced file once into owned bytes;
2. validate, resolve, normalize, and encode immutable
   `theme_package_install_wire_v1` from those bytes outside the lock;
3. lock the injected store, check expected revision/nonoverflow, atomically
   replace its sole wire-backed aggregate, then unlock;
4. apply exact scalar projection to parent WM and GUI;
5. emit `ThemeChangedV1` with committed identity/revision;
6. hand wire to each worker, invalidate revision-keyed Web artifacts, and
   publish a Web external frame only after matching acknowledgement and frame.

No-op identity/content, invalid source/wire, stale revision, max revision, or
lock failure returns a typed error and performs no write or notification. A
post-commit worker failure is `web-frame-unavailable` for the new revision,
never a stale old frame masquerading as current. `ThemeChangedV1` remains a
post-commit notification only; it is neither a mutable candidate nor a
synchronization primitive.

## Web and CSS Changes

`simple_web_content_render_request_with_theme` receives a cached snapshot (or
its CSS/fingerprint) rather than branching on theme-name strings. Request and
content-cache revisions include the material hash. Structural WM layout CSS is
appended after package CSS but contains no visual palette.

The production Style/computed-style model gains ordered shadow layers and
backdrop blur/saturation. Draw IR style projection preserves the same values.
The older DOM accessor layer must return stored semantics rather than constant
zeros/empty arrays so `layout_paint` is internally coherent. Existing feature
gap tests change backdrop blur from known-unsupported to supported or explicit
capability fallback.

## Rendering Algorithm

For each glass box: paint prior background; render ordered outer shadows;
sample/blur/saturate the bounded backdrop when available; composite translucent
surface; paint inset shadows, border, then content/text. When unavailable or
reduced transparency is requested, paint the declared solid fallback and emit
realized capability state. Never silently substitute opaque default colors.

### CPU-composited Draw IR material slice

`draw_ir_adv` is the canonical styled-rectangle lowerer. When its existing
`backdrop-filter-capability` value is
`engine2d-cpu-composited-material-v1`, it constructs an
`Engine2dGlassMaterialConfig` and delegates the pixel math to
`engine2d_draw_ir_glass_material_pixels`. The helper accepts only an in-bounds
rectangle and a framebuffer whose length matches the declared dimensions. It
uses `i64` intermediates and caps output plus horizontal work at 67,108,864
pixels; it clamps blur to `0..4`, saturation to `0..3000` thousandths, and
radius to half of both surface extents.

The helper reads the pre-surface framebuffer, performs a deterministic
separable box blur, applies saturation, clips each output pixel to the rounded
surface, and alpha-composites the translucent `background-color`
(`window_fill_rgba`) or the normalized two-stop vertical gradient.
`DrawIrCommand.color` remains opaque `solid_fallback_rgba` for native-safe
transport; it is not the selected glass tint. Requested blur `30px` is
explicitly realized as blur `4px`, with realized blur/saturation keys and a
reduction reason. `draw_ir_adv` then paints the existing border logic. The WM
body is the requested material surface; the titlebar remains `not-requested`
for backdrop material in this slice. The fallback witness
`cpu-composited-material` with reason `native-device-backdrop-path-pending`
means CPU realization exists while native device realization is still pending;
it must never be reported as a device fallback/readback receipt.

Simple Web now preserves glass layers only for the byte-exact
`engine2d-cpu-composited-material-v1` opt-in. All other modes retain the named
opaque fallback. Unsupported/multiple image syntax stays visible as a raw
rejection witness instead of being silently projected into the supported typed
gradient.

The canonical WM Web producer places that exact opt-in on the
`.wm-app-content.widget-panel` wrapper. It does not restate Aetheric colors or
effects: the generated theme package remains authoritative for
`rgba(31,31,33,0.80)`, the two alpha-gradient stops, and
`blur(30px) saturate(170%)`. The wrapper retains a named opaque color only as
fail-closed metadata. A stable `wm-app-content` id exists for computed-style
evidence and is not a second theme selector.

### Simple Web CSS-to-material source implementation

The implementation order is fixed:

1. Remove the unconditional opacity/gradient destruction from
   `simple_web_html_layout_renderer_declarations.spl`. `Style` retains cascaded
   backdrop text, translucent base color, normalized gradient stops, raw layer
   order, and radius.
2. Replace the unconditional `data-wm-theme-fallback=solid-material` rewrite in
   `simple_web_html_layout_renderer_core.spl` with an explicit material policy.
   The named `data-wm-theme-bg`/`fg` values remain fallback inputs, not
   replacements for retained CSS semantics.
3. In `simple_web_html_layout_renderer_paint_layout.spl`, keep the opaque
   fallback in `DrawIrCommand.color`; place the cascaded translucent base in
   `background-color`; emit the material request, required realized
   blur/saturation keys, reduction reason, and normalized layer metadata.
   Missing realized keys fail back to the opaque command color.
4. Extend the canonical Engine2D helper from “surface or gradient” to ordered
   “surface then alpha-gradient” composition so Aetheric's layered CSS is not
   flattened. Clamp/reduction and work-cap witnesses remain inspectable.
5. Keep `simple_web_layout_engine2d_cpu.spl` fallback-only. The advanced
   Engine2D path consumes the material keys; the legacy executor consumes only
   `DrawIrCommand.color`.
6. Extend `WebRenderMaterialFallbackProvenance`, `WebRenderArtifact`, and
   `wm_content_frame_web_provenance_valid` with a distinct
   `cpu-composited-material` realization and semantic hash. Existing
   `solid-material` receipts remain valid only for the fallback lane.

The source implementation follows this order, but no phase may promote Web
support until a focused
CSS -> computed Style -> Draw IR -> independent CPU pixel test proves base,
gradient alpha, rounded corner, backdrop sample, and opaque fallback from the
same request. Native Vulkan/Metal, SIMD, event, host, and QEMU evidence remain
separate later phases.

### Metal device glass operation

Metal material execution is an operation receipt, not an inference from the
final framebuffer. `DrawIrRenderTarget.draw_ir_apply_glass_material` is the
single narrow backend hook; the generic `RenderBackend` interface remains
unchanged. A Metal target admits `metal-device-glass-v1` only after one command
buffer completes two ordered compute encoders:

1. `kernel_glass_snapshot` copies the current device framebuffer into a
   transient immutable device buffer;
2. `kernel_glass_material` reads that snapshot, performs the bounded
   blur/saturation/surface/gradient operation, and writes the existing device
   framebuffer.

Separate encoders establish snapshot-before-material ordering and prevent
in-place blur races. The snapshot never enters Draw IR or a Web artifact.
Missing optional pipelines, invalid configuration, or pre-submit failures fall
back to the existing CPU/solid policy without a device claim. A submitted
operation whose completion is unknown poisons the device material state and
must not run the CPU compositor over a possibly mutated framebuffer.

The MSL compositor is required to match the CPU oracle for straight-alpha
source-over, including translucent destinations: destination RGB is weighted
by destination alpha, and output RGB is unpremultiplied by output alpha. The
live Metal contract samples outside, rounded-corner, and center pixels over a
translucent backdrop against the scalar CPU result.

`Engine2dDrawIrAdvResult` carries device-glass count, execution target,
framebuffer handle, and device identity separately from final
`readback_source`. Web promotion requires the producer witness count, completed
Metal operation count, exact execution target, positive handle/identity, zero
CPU count, and final `device_readback`. Only then may the artifact use
`metal-device-composited-material`; a device readback after CPU composition
remains `cpu-composited-material`.

The existing macOS ARM64 row-blend ABI can accelerate only the final blend
passes with real NEON. It does not prove NEON blur/saturation and its global hit
counter is not operation-specific, so no `glass-neon` receipt is admitted in
this phase.

## Evidence Model

`wm-glass-theme-evidence-v1` separates requested semantics from realized
capabilities. Per blur/shadow/gradient/font/GPU/readback capability record:
requested, `available|unavailable`, proof rung, implementation, fallback used,
fallback kind/reason and realized hash. `unknown` is invalid.

The realized fallback hash canonicalizes the actual emitted, visible paint
commands after cascade and fallback selection. Hidden/non-emitted nodes are
excluded, equivalent CSS color spellings converge on one value, and both the
software and Draw IR paths use the same ordering and canonical representation.
The typed evidence travels beside pixels in `WebRenderArtifact`.

GPU proof order is BAR2 mapped, hello acknowledged, backend selected, Draw IR
submission accepted, device receipt valid, readback presented, independent QMP
`pmemsave`. Record highest passed and first unavailable.

The CPU-composited unit algorithm is not itself a CPU-SIMD execution witness,
native Vulkan/Metal execution, host framebuffer capture, QEMU screenshot, or
event/performance measurement. Those evidence rungs remain separately gated.

## Error Handling

Invalid package/schema/hash/snapshot drift fails before theme installation.
Unknown capability, compatibility renderer, legacy entry, stale revision,
wrong-process capture or mismatched hash rejects evidence. Runtime inability to
blur uses the named solid fallback and remains operational but cannot masquerade
as native blur.

## Performance

Measure cached warm host startup, frame p50/p95/max, input-to-present, QEMU
launch-to-first-themed-frame, QEMU themed-frame latency and max RSS. Package
parsing/generation is outside hot paths; frame rendering performs no file scan,
CSS package load or subprocess.
