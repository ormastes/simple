<!-- codex-design -->
# Showcase apps architecture

`showcase_catalog` is the identity and metadata owner. It exposes three entries and maps each entry to a render/state module plus standalone, host-WM, and SimpleOS-WM adapters.

Title and identity mapping is stable and reused by all layers:

- `graphics_2d_showcase` → catalog `2D Rendering Showcase`; window/app titles are backend-stamped:
  - standalone: `2d_showcase_backed_<backend_token>`
  - host/installed: `2d_showcase_backed_<backend_token>`
- `web_standards_showcase` → catalog `Web Standards Showcase`; window/app titles are backend-stamped:
  - standalone: `web_showcase_backed_<backend_token>`
  - host/installed: `web_showcase_backed_<backend_token>`
- `gui_widget_showcase` → catalog `Widget Showcase`; window/app titles are backend-stamped:
  - standalone: `gui_showcase_backed_<backend_token>`
  - host/installed: `gui_showcase_backed_<backend_token>`

`<backend_token>` is normalized by the engine layer (`cpu`, `software`, `simd`, `cpu_simd`, `cpu-simd`, `simd_cpu`, `simd-cpu`, `vulkan`, `metal`, `tauri`, `electron`, explicit `simple_gui_simple_*`).

Application modules own deterministic state, rendering, hit testing, and semantic snapshots. Surface adapters own only window creation, WM/IPC transport, event conversion, presentation, and evidence capture. The host adapter may use the existing filesystem bridge; the SimpleOS adapter must use installed-app identity and OS WM/IPC/shared-framebuffer facilities.

The browser application loads the canonical standards page through BrowserApp. Placeholder renderers must return explicit unsupported diagnostics and are excluded from successful surface evidence. Engine2D evidence includes backend handle/provenance and same-frame device readback where the backend supports it.

Backend selection belongs to app entrypoints:

- `widget_showcase_gui.spl` first honors `--backend=<name>`, then `SIMPLE_GUI_BACKEND`, then defaults to `software`.
- `graphics_2d_showcase_gui.spl` (standalone) reads `SIMPLE_GUI_BACKEND` and defaults to `software`; host-WM child path defaults to `cpu_simd`.
- `web_render_file_gui.spl` and `web_standards_showcase_gui.spl` read `SIMPLE_GUI_BACKEND` and default to `cpu_simd`.
- Host-WM launchers forward the env var unchanged to children and verify requested/actual backend match.

Catalog IDs are stable across surfaces; installed paths are mappings, not new logical identities. This prevents launcher, WM scene, docs, and tests from drifting into separate app definitions.

## ARM64 QEMU evidence adapter

The ARM64 real-screen fixture consumes the same target-neutral 2D render owner
as the standalone app. `graphics_2d_showcase_core` returns the canonical pixel
frame through a concrete target-selected `Engine2D`; the guest compositor owns
those pixels through `WM_CONTENT_KIND_PIXEL_SURFACE`. The ordinary WM scene
builder then embeds that content as an image command in its
`DrawIrComposition`, so window chrome, focus, input repaint, NEON execution,
and RAMFB presentation remain on the production WM → Draw IR → Engine2D path.

This fixture is live QEMU acceptance evidence, not installed-launcher evidence.
The catalog's `simpleos_wm_ready` flag remains false until the manifest at
`/sys/apps/graphics_2d_showcase.smf` is launched through the catalog action.
