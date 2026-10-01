# Chrome Rendering Module as a Dynlib, Vulkan-Backed — Research (2026-09-11)

Scope: a Chromium rendering module Simple loads as a **shared library** through the
existing SFFI host-process dynlib facade, plus the showcase and perf-check infra around
it. GPU-offload infrastructure is owned by other lanes and is excluded.

## 1. What already exists (do not rebuild)

### 1.1 There is already a "chrome dynlib" — but it is a broker, not an embed
`tools/chromium-primitive-oracle/chromium_primitive_oracle.spl` builds
`libsimple_chromium_primitive_oracle.{dylib,so,dll}` via
`bin/simple compile ... --native --shared --strip`
(`scripts/check/build-chromium-primitive-oracle.shs:11,388`). Frozen C ABI v1
(`test/fixtures/chromium_primitive_oracle/simple_chromium_primitive_oracle.h:20-27`):

```
uint32_t simple_chromium_oracle_abi_version(void);
int64_t  simple_chromium_oracle_create(const uint8_t *config, uint64_t len);
int32_t  simple_chromium_oracle_run_json_into(int64_t h, ...);
int32_t  simple_chromium_oracle_last_error_into(int64_t h, ...);
int32_t  simple_chromium_oracle_destroy(int64_t h);
```

Internally it **spawns** a pinned Electron broker (Electron 42.5.0 / Chrome
148.0.7778.271) once per fixture request and returns its CPU `capturePage` result. The
README is explicit that this is never promoted to device-origin GPU evidence. So the
existing module is a *process broker wrapped in a dylib*, not an embedded Chromium.

### 1.2 The host-process dynlib pattern to reuse verbatim
`src/lib/nogc_sync_mut/gpu/chromium_reference_oracle_sffi.spl:236-287` is the canonical
pure-Simple external-library load. Note this is **not** `os.posix.dynlib`
(`doc/07_guide/lib/api/dynlib_api.md` — that is the SimpleOS kernel registry). The host
path is:

- `file_hash_sha256(path)` vs a manifest digest **before** load (`:244`)
- `DynLib.load(path)` -> `lib.sym(name)` per required symbol (`:250-258`)
- re-digest **after** load, reject if the artifact changed mid-load (`:265`)
- `chromium_oracle_validate_library_probe` — exact required-symbol-set match, ABI version
  equality, bounded request/response caps (1 MiB / 4 MiB)
- call through `spl_wffi_call_i64(sym, args, argc)`; release with `spl_dlclose`
- every entry point is `@unsafe(reason:..., capabilities: [ffi, raw_ptr])`

Every buffer-returning call is the `*_into(handle, buf, cap)` idiom with an out-length —
no Simple-side ownership of C memory. A new Chrome module must copy this shape exactly.

### 1.3 Chrome is launched two ways today; neither embeds
1. **Electron broker** — the oracle path above, pinned by broker SHA-256 + npm lockfile
   SHA-256, versions re-verified inside the broker before a window is created.
2. **Headless process spawn** — `test/05_perf/web_render_chrome/chrome_runner.spl:30-86`
   probes `/usr/bin/google-chrome{,-stable}` and runs
   `--headless=new --disable-dev-shm-usage --no-first-run --screenshot=<png> file://<html>`,
   recording PNG bytes + SHA-256. `check-chrome-simple-web-comparison.shs:133-193` then
   projects both sides to `chrome_frame_ms_p95` / `simple_frame_ms_p95` and emits
   `chrome_simple_web_status=admitted|skipped` with a `..._reason` and
   `chrome_simple_web_ratio_x1000`. `check-chrome-html-compat-geometry-manifest-evidence.shs`
   and `check-electron-vulkan-web-parity.shs` add geometry-manifest and ARGB-bitmap parity;
   `check-html-css-renderdoc-goal-status.shs` aggregates `*_status=` rows fail-closed.

**Neither path hands over a GPU texture.** Both are CPU captures of a separate process.

### 1.4 Vulkan proof vocabulary is already fixed
`doc/07_guide/tooling/renderdoc_capture_infra.md:748-790` — keys are
`gui_web_2d_vulkan_<subject>_<field>`; browsers on this host record
`gui_web_2d_vulkan_chrome_vulkan_reason=vulkan-angle-unavailable` (also emitted at
`scripts/check/check-renderdoc-electron-html-gate.shs:226`), while the Simple lane
records `gui_web_2d_vulkan_simple_status=pass`,
`gui_web_2d_vulkan_simple_backend_name=vulkan`. RenderDoc rows are
`rdoc_capture_status=unavailable`, `rdoc_capture_reason=missing-renderdoc`.
Verified on this host 2026-09-11: `command -v renderdoccmd` -> not found.

### 1.5 The Simple-side showcase already has the catalog
`.spipe/web_renderer_vulkan_4k_showcase_hardening/state.md` owns AC-1..3: a typed
`WebRenderableFeatureInventory` v1 (113 HTML names, all 284 CSS names), seven canonical
tabs, accessible tablist/tabpanel markup, and a **shared fixture composer** that injects
the identical inventory-expanded markup into both the Simple runner and the Chrome
harness. That lane's AC-6/7 is exactly the Chrome-side comparison slot this work fills.
**Do not write a second catalog generator.** The prior `chrome-class-browser-plan` lane
(CLOSED 2026-05-20) shipped only a roadmap doc (`ef320825a97`, 35 lines) — no code.

## 2. Which embeddable Chromium (web facts UNVERIFIED — no network in this sandbox)

| Option | License | Approx size | Offscreen API | GPU handover | Chromium? |
|---|---|---|---|---|---|
| **CEF (libcef)** | BSD-3 | ~150-200 MB binary dist | `CefRenderHandler::OnPaint` (CPU BGRA) and `OnAcceleratedPaint` (shared texture) when `windowless_rendering_enabled` + `shared_texture_enabled` | Linux: dma-buf plane fds -> `VK_EXT_external_memory_dma_buf`; Windows: D3D11 shared handle; macOS: IOSurface -> MoltenVK | yes |
| Chromium headless shell | BSD-3 | ~120 MB | CDP `Page.captureScreenshot` | none (separate process) | yes |
| Ultralight | proprietary/paid | ~10 MB | CPU/GPU driver interface | app-supplied GPU driver | **no** (WebKit-derived) |
| Servo (libservo) | MPL-2.0 | ~80 MB | embedder API, unstable | surfman surface | **no** |
| WKWebView | system | 0 | `takeSnapshot` | IOSurface, private | **no**, macOS-only |

**Recommendation: CEF.** It is the only candidate that is simultaneously (a) real
Chromium, (b) a genuine shared library loadable by `DynLib.load`, and (c) capable of
accelerated offscreen output. Headless shell is what the repo already has and is a
process, not a library. The three non-Chromium options fail the user's stated intent
("chrome rendering module").

**Honest caveats:**
- **macOS**: ANGLE on macOS backs onto Metal; `--use-angle=vulkan` is not a shipped
  backend there. Per `renderdoc_capture_infra.md:748`, this host must record
  `vulkan-angle-unavailable` unless a Chromium log proves `angle=vulkan`. Do not infer.
- **macOS subprocesses**: CEF requires a separate helper `.app` bundle for its render/GPU
  subprocesses. Whether that can be satisfied when libcef is `dlopen`ed from a plain CLI
  binary (no enclosing bundle) is **UNVERIFIED** and is the single largest macOS risk.
- **RenderDoc**: `renderdoccmd` absent on this host; every RenderDoc row is `blocked`.
- **Distribution**: the CEF binary must be pinned by SHA-256 exactly as the Electron
  broker is. The download itself is blocked in this sandbox (no curl/wget/network).

## 3. The dynlib boundary in Simple

### 3.1 Why a C shim (and not pure Simple) at the boundary
CEF's C API is a struct-of-function-pointers, and offscreen delivery is a **callback into
the host** (`cef_render_handler_t::on_paint` / `on_accelerated_paint`). The repo's FFI
calls *forward only* — `spl_wffi_call_i64` / `rt_dyncall_0..6`. A search for a C->Simple
trampoline facility across `src/runtime` and `src/lib/nogc_sync_mut/ffi` finds only
`src/runtime/startup/baremetal/runtime_minimal.c`, i.e. nothing usable on the host path.
Therefore the CEF callbacks must be owned by C. This is the pure-Simple-first rule's
"C boundary" case, and it is satisfied by shipping a **Simple twin** of the shim's pure
logic (frame-state machine, bounds validation, receipt field assembly) checked by the
existing dual-run twin gate (`scripts/check/check-dual-run-shadow.shs`), not by pretending
the boundary can be pure.

### 3.2 Proposed ABI v1 — `simple_chrome_render_*` (10 symbols, mirrors the oracle idiom)

```
uint32_t simple_chrome_render_abi_version(void);          /* == 1 */
int64_t  simple_chrome_render_create(const uint8_t *cfg_json, uint64_t len);
int32_t  simple_chrome_render_load_html(int64_t h, const uint8_t *html, uint64_t len);
int32_t  simple_chrome_render_load_url(int64_t h, const uint8_t *url, uint64_t len);
int32_t  simple_chrome_render_resize(int64_t h, uint32_t w, uint32_t h_px, double scale);
int32_t  simple_chrome_render_frame(int64_t h, uint64_t timeout_ms);   /* pumps to 1 complete frame */
int32_t  simple_chrome_render_read_pixels_into(int64_t h, uint8_t *buf, uint64_t cap, uint64_t *out_len);
int32_t  simple_chrome_render_event(int64_t h, const uint8_t *evt_json, uint64_t len);
int32_t  simple_chrome_render_last_error_into(int64_t h, uint8_t *buf, uint64_t cap, uint64_t *out_len);
int32_t  simple_chrome_render_destroy(int64_t h);
```

Bounded exactly like ABI v1 above (1 MiB request cap, response cap derived from
`w*h*4` plus a hard ceiling). The Simple binding
`src/lib/nogc_sync_mut/gpu/chrome_render_module_sffi.spl` copies
`chromium_oracle_load`'s digest-before / symbol-exact / digest-after / `spl_dlclose`
sequence and its `@unsafe(capabilities: [ffi, raw_ptr])` annotations verbatim.

### 3.3 Frame path: v1 is a CPU BGRA upload, and that is a measured constraint
Engine2D's Vulkan backend accepts images only as `pixels: [u32]`
(`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:176`,
`_vulkan_scaled_image_args_valid`). There is **no external-memory import entry point**
anywhere in `src/lib/gc_async_mut/gpu/engine2d/`. So:

- **v1**: `render_frame` -> `read_pixels_into` -> existing scaled-image upload ->
  Engine2D -> Vulkan. One CPU round trip per frame. Honest, and measurable.
- **Zero-copy (deferred, blocked row)**: `OnAcceleratedPaint` -> Linux dma-buf fd ->
  `VK_EXT_external_memory_dma_buf` + `VK_KHR_external_memory_fd`; macOS IOSurface ->
  MoltenVK `VK_EXT_metal_objects`. This is **new runtime work** (new `rt_*` surface + new
  Engine2D import API) and must not be smuggled into the shim slices.

## 4. Showcase and perf-check contract

Both showcases consume the **same** catalog: the 4K lane's `WebRenderableFeatureInventory`
and its shared fixture composer, rendered as the seven canonical tab pages. The Chrome
module selects a tab by dispatching a click through `simple_chrome_render_event`; the
Simple side uses its existing native tab path. Apples-to-apples requires identical
viewport, device scale, and inventory version — all three go in the receipt.

Receipt: `key=value` lines, prefix `chrome_dynlib_`, mirroring `electron_gate_*` and
`chrome_simple_web_*` style. Required fields:

```
chrome_dynlib_binary_path=        chrome_dynlib_binary_sha256=
chrome_dynlib_lib_path=           chrome_dynlib_lib_sha256=
chrome_dynlib_abi_version=        chrome_dynlib_cef_version=
chrome_dynlib_inventory_version=  chrome_dynlib_viewport=3840x2160
chrome_dynlib_tab=                chrome_dynlib_backend_reported=
chrome_dynlib_vulkan_proof_mode=  chrome_dynlib_vulkan_reason=
chrome_dynlib_wall_s=             chrome_dynlib_frame_ms_p50=
chrome_dynlib_frame_ms_p95=       chrome_dynlib_rss_mb=
chrome_dynlib_pixel_diff_status=  chrome_dynlib_pixel_mismatch_count=
chrome_dynlib_rdoc_capture_status=  chrome_dynlib_status=
chrome_dynlib_reason=
```

`chrome_dynlib_vulkan_proof_mode` draws only from the existing repo vocabulary —
`device-readback`, `log-proven`, or the negative `vulkan-angle-unavailable` carried in
`..._reason`. Verdicts are fail-closed and exactly four:
`passed` / `failed` / `environment-blocked` / `could-not-complete-in-time`. A missing
field, an unresolvable binary, an absent library, or a zero-count scan is
`could-not-complete-in-time` or `environment-blocked` — never `passed`. Binary identity is
recorded per `.claude/rules/commands.md`: `readlink -f` plus size and mtime, alongside the
SHA-256 of the loaded library.

## 5. Open / unverified

- All CEF facts in §2 are from model knowledge; no network fetch was possible
  (curl/wget/WebFetch blocked, no `simple_ctx_fetch_and_index` in this agent's toolset).
  Sizes, license and API names must be re-verified against cef-builds before S1 lands.
- CEF-on-macOS helper-bundle feasibility under `dlopen` from a non-bundled CLI: UNVERIFIED.
- Whether `DynLib.load` tolerates a library with its own subprocess/thread model
  (CEF spawns a GPU process and runs a message loop): UNVERIFIED; S1's second stage exists
  to answer exactly this.
