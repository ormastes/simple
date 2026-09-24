# TL;DR — Chrome dynlib, Vulkan-backed (2026-09-11)

- **Use CEF (libcef, BSD-3)** — only candidate that is real Chromium AND a shared library AND has accelerated offscreen output. Headless shell is a process; Ultralight/Servo/WKWebView are not Chrome.
- **A "chrome dynlib" already exists but is a broker**: `libsimple_chromium_primitive_oracle` spawns a pinned Electron and returns a CPU capture.
- **Reuse its load pattern verbatim** (`chromium_reference_oracle_sffi.spl:236-287`): sha256 before load, `DynLib.load` + exact symbol set, sha256 after, `spl_wffi_call_i64`, `spl_dlclose`, `*_into(buf,cap)` out-params.
- **A C shim is required**: CEF delivers frames via callbacks (`on_paint`) and the repo FFI calls forward only (no host C->Simple trampoline). Ship a Simple twin for the dual-run gate.
- **New ABI v1 is a sibling of the oracle's frozen 5-symbol ABI**, not a replacement; same `nm`-exact symbol-set discipline, disjoint `simple_chrome_render_` prefix.
- **v1 frame path is CPU BGRA**: Engine2D Vulkan takes images only as `pixels: [u32]` (`engine2d/backend_vulkan.spl:176`); no external-memory import exists. Zero-copy is deferred (B5).
- **Reuse the 4K lane's catalog** (`web_renderable_feature_inventory.spl`, 7 tabs, shared composer). This lane fills that lane's AC-6/7.
- **Host blockers:** `renderdoccmd` absent -> RenderDoc rows blocked; Chrome ANGLE Vulkan unavailable on macOS -> `vulkan-angle-unavailable`. Resume on Linux.
- All external CEF facts are **UNVERIFIED** (no network in this sandbox).

```sdn id=chrome_dynlib_vulkan_render.overview hash=sha256:auto render=ascii
@layout dag
@direction LR

SharedCatalog -> ChromeShowcase
SharedCatalog -> SimpleShowcase
ChromeShowcase -> ChromeBinding
ChromeBinding -> CShim
CShim -> libcef
libcef -> CpuBgraFrame
CpuBgraFrame -> Engine2D
SimpleShowcase -> Engine2D
Engine2D -> VulkanBackend
VulkanBackend -> Receipt
Receipt -> PerfCheck
```
