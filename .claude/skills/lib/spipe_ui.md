# SPipe UI Skill — GUI sanity checks (pure-Simple lane)

The pure-Simple GUI lane is verified by **three canonical check apps**, one per
rendering surface. After any GUI / engine2d / web-render change, run all three
and verify the **framebuffer** (not the screenshot — see the oracle rule below).

On macOS the pure-Simple lane = **Engine2D CPU/NEON** (aarch64) + **Metal** (GPU).

> **Linux Vulkan-backed browser lane IS available (verified 2026-06-25).** Do not
> assume the Vulkan/RenderDoc lane is macOS-only — on the Ubuntu host (Intel RPL-P,
> Mesa ANV, Vulkan 1.4.318) **Electron `v42.5.0` and Chrome `139` both render through
> Vulkan** (ANGLE → Vulkan, confirmed), and **RenderDoc `v1.44` CLI is installed**
> (`/opt/renderdoc`, on `PATH`, Vulkan-capable). Electron project: `~/electron-vulkan`
> (verify: `electron gpu-probe.js --ozone-platform=x11` → `vulkan: enabled_on`).
> **Mandatory Wayland gotcha:** force `--ozone-platform=x11` or Chromium falls back to
> software. RenderDoc `.rdc` capture of Electron works via
> `~/electron-vulkan/capture-renderdoc.sh`; Chrome GPU-process hooking is blocked by a
> `localtime64_r` crash under `--disable-gpu-sandbox`. Full runbook:
> `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md` § Linux Status.

## The 3 main GUI check apps

| # | Surface | App | What it must show |
|---|---------|-----|-------------------|
| 1 | **2D rendering** | `examples/06_io/ui/engine2d_shapes_gui.spl` | text, rect (filled/outline), circle, line, gradient, rounded-rect — bit-exact across CPU-NEON and Metal |
| 2 | **GUI widgets** | `examples/06_io/ui/widget_showcase_gui.spl` | the full widget catalog (button, checkbox, radio, input, dropdown, slider, switch, list, table, tree, tabs, progress, card, …) with legible labels |
| 3 | **HTML/web rendering** | `examples/06_io/ui/web_render_file_gui.spl <file.html>` | real HTML+CSS (header/nav, hero, flex two-column main+sidebar, form, footer) via the pure-Simple web layout → Engine2D |

Canonical app IDs are `graphics_2d_showcase`, `web_standards_showcase`, and
`gui_widget_showcase`. Their canonical launch surfaces are `standalone`,
`host_wm`, and `simpleos_wm`; platform adapters must not invent alternate IDs.

### Canonical showcase manual

For each supported app/surface pair:

1. Launch the app by canonical ID and select the named surface.
2. Capture a UI snapshot and find the app or control by canonical ID, visible
   text, or semantic role.
3. Act on a semantic control. For the widget showcase, exercise at least one
   stateful control such as button, checkbox, switch, or slider.
4. Read action history and assert the dispatched target and local coordinates
   where relevant; snapshot again and assert the semantic state changed.
5. Capture the framebuffer and assert it is nonblank. Record drawing backend,
   processing/offload backend, device/handle provenance, and fallback state from
   the same run.

Fail the scenario for dummy or blank frames, source-assertion-only evidence,
synthetic handles claimed as real devices/backends, action logs without a
post-action semantic-state assertion, or backend labels without same-run
provenance. A screenshot is supplemental layout evidence, not a replacement for
snapshot/find/act/history plus semantic state and framebuffer checks.

Backend-specific 2D variants (same scene, different backend) for parity work:
`engine2d_cpu_simd_gui.spl` (CPU-NEON) and `engine2d_metal_gui.spl` (Metal).

> **These 3 apps render STATIC, NON-INTERACTIVE scenes** — render-surface sanity
> checks, not the interactive GUI. (#3 `web_render_file_gui` uses the real web
> layout → Engine2D renderer; #2 `widget_showcase_gui` and #1 `engine2d_shapes_gui`
> draw primitives directly — fine for a primitives/widget-catalog demo, but NOT a
> template for building an interactive app.) For a real interactive app, do NOT
> hand-draw one. See the next section.

## Showcase apps — files, surfaces, and honest verification

Each canonical app has a standalone source + `_gui` window wrapper, launchable
on **3 surfaces** (standalone / host-WM / SimpleOS WM):

| App (canonical ID) | Standalone / `_gui` source | Host-WM adapter |
|---|---|---|
| `graphics_2d_showcase` | `examples/06_io/ui/graphics_2d_showcase.spl` + `graphics_2d_showcase_gui.spl` | `wm_graphics_2d_showcase_gui.spl` |
| `web_standards_showcase` | `web_standards_showcase_gui.spl` / `web_render_page_ppm.spl` rendering `browser_common_elements_showcase.html` | `wm_web_standards_showcase_gui.spl` |
| `gui_widget_showcase` | `widget_showcase_gui.spl` | `wm_widget_showcase_gui.spl` |

SimpleOS WM surface: no showcase is accepted into the installed launcher yet —
`simpleos_wm_ready` is `false` for all three.

**Verified headless run recipe** — fresh-seed binary (`bin/simple` traps on
dict-heavy compiles for these apps; see
`doc/08_tracking/bug/stage4_compiled_dict_no_growth_2026-07-11.md`):

```bash
SIMPLE_LIB=src SHOWCASE_RESOLUTION=320x240 \
  src/compiler_rust/target/bootstrap/simple run examples/06_io/ui/graphics_2d_showcase.spl
SHOWCASE_PPM=/tmp/widgets.ppm SIMPLE_LIB=src SHOWCASE_RESOLUTION=1280x720 SIMPLE_TIMEOUT_SECONDS=1200 \
  src/compiler_rust/target/bootstrap/simple run examples/06_io/ui/widget_showcase_gui.spl
```

`SHOWCASE_RESOLUTION` defaults to 4K (3840x2160), `SHOWCASE_DPI` to 300. Full
4K/8K is **compiled-lane-gated** (interpreter throughput ~5k px/s) — verify at
a small explicit rung (e.g. `320x240`) rather than trusting the 4K default to
finish under the interpreter within `SIMPLE_TIMEOUT_SECONDS`.

**Honest verification — analyze the PPM, never trust file size.** Decode the
P6 PPM and count distinct colors / nonzero pixels: a uniform background-color
frame (the interpreter-budget-wall failure mode seen at 4K on the web
showcase) has a large file size but near-zero distinct colors.
`graphics_2d_showcase` additionally self-gates: it computes
`nonzero`/`checksum`/`semantic_differences` (5 independently rendered
primitive samples that must differ pairwise) from a real
`read_pixels_with_source()` device readback and exits 1 if any check fails —
treat that exit code as an anti-fake gate, not just a crash check.

**Lane reality:** the interpreter is the only lane currently reaching these
apps; full 4K and the web-standards showcase both time out / degrade at full
resolution — do not claim a 4K or web-showcase PASS without a same-run
small-rung result or an explicit budget-fix citation. Full per-app lane
status and all 3 surfaces: `doc/07_guide/ui/showcase_apps.md`.

## Interactive GUI (the REAL pipeline) — do NOT hand-draw a new one

⚠️ **Hand-drawing a GUI by calling engine2d primitives (`draw_rect` / `draw_text`,
`draw_circle`, …) to lay out widgets yourself bypasses the real UI architecture
and is considered FAKE.** It reinvents layout/state/event routing that already
exists. Use the builder → `render_html_tree` → web-renderer pipeline below, or
extend the existing interactive host — never reinvent widgets with raw 2D ops.

**To just open ONE GUI window (default — not the WM):** present a `[u32]` buffer to
a single winit window via `std.io.window_winit` and **re-present continuously** in
the loop — model: `examples/06_io/ui/web_engine2d_gui.spl` (its `iters % 200`
re-present). On macOS the window only composites if you keep presenting; a
render-on-dirty-only loop (like the WM) leaves the window blank. Do NOT reach for
the multi-window compositor unless you actually need multiple windows.
⚠️ `web_engine2d_gui.spl`'s `demo_html()` uses the **corpus/heuristic** renderer at
32×24 (a degenerate marker demo — titlebar fills the whole height). For CORRECT
content render a real widget tree (builder → `render_html_tree`, pipeline below) or
a real HTML file through the layout renderer — not the corpus demo markers.

**For MULTIPLE windows (advanced — the MDI WM):** `src/os/hosted/hosted_entry.spl`
wires a `HostCompositor` (`src/os/compositor/host_compositor_entry.spl`) seeded by
`seed_host_compositor_shared_mdi` (`src/os/compositor/shared_mdi_host_seed.spl`),
rendering **Simple Web MDI app content** through `HostedWinitBufferBackend`
(`src/os/compositor/hosted_backend_winit.spl`), with REAL event routing:
`comp.pointer_move(x, y)`, `comp.handle_left_button(pressed)` (click-focus,
titlebar drag, close-X) and keyboard Tab/W/M/R/Esc. (Known bug: its render-on-dirty
loop leaves content blank on macOS — needs the continuous re-present above.)
For selected-font claims, this hosted lane is still a compatibility path:
`HostCompositor.render_frame` lowers through direct backend/pixel-buffer
renderers. Do not call it canonical until the real frame owner executes
`SharedWmScene -> DrawIrComposition -> Engine2D`; do not add a private font
loader, renderer, atlas, or cache to the platform backend.

**The real widget → pixels pipeline** (used by the office apps word/sheets/mail/
planner and the WM — model app `src/app/wm_compare/production_gui_web_renderer_parity.spl`):

```
common.ui.builder      button(id,label,action) / text_field / list_widget / scroll
                       / column / row / panel / build_tree_with_title(root,title,theme)
  -> common.ui.state.init_state(tree)
  -> app.ui.render.html_widgets.render_html_tree(state.tree.root_node(), state)   # -> HTML
  -> simple_web_render_html_to_pixels_with_engine2d_backend(html, w, h, "cpu_simd")  # -> [u32]
```

Real pixel→widget hit-testing already exists too: `shared_wm_translate_pointer_event`
in `src/lib/common/ui/window_scene.spl` (returns component kind, local coords,
target id, callback/window identity).

**Verify with the framebuffer/logic gate, not a screenshot:**
`scripts/check/check-shared-wm-renderer-unification-evidence.shs` (expects
`shared_wm_renderer_unification_status=pass`, `logic_passed >= 4`).

**Fast live-interaction status:** the pure-Simple web render is REAL but
interpreter-bound (~minutes/frame, not live-interactive). The fast "real IR" path
is UI model → Draw IR → Engine2D executor `engine2d_draw_ir_adv_batch`
(`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`), but the widget-tree→Draw IR
converter is **NOT built yet** (the "preferred next refactor" in
`doc/04_architecture/ui/simple_gui_stack_tldr.md`). So today: live interaction is
via Draw IR (converter TBD) or the electron/tauri/chromium host shells.

**macOS caveat:** the hosted winit window composites, but on-screen content can be
blank — the documented winit present bug
(`doc/08_tracking/bug/macos_winit_window_not_displayed_2026-05-28.md`). Trust the
framebuffer/logic gate, not the live window, on macOS.

### Web-render backend comparison (pure_simple vs chromium)

`examples/06_io/ui/web_render_backend_gui.spl` renders the **same** HTML page
through one `WebRenderBackend` interface on either engine — `pure_simple` (Simple
layout → Engine2D raster in a winit window) or `chromium` (a **live, interactive**
Electron `BrowserWindow`). Use it to compare Simple's own renderer against real
Chromium. Honest bit-level gate: `check-electron-simple-web-engine2d-bitmap-evidence.shs`
(`mismatch=0`, two independently produced artifacts — never memorized pixels).
Guide: `doc/07_guide/ui/web_render_backend.md`.

```bash
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl pure_simple 384x288
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_render_backend_gui.spl chromium 1280x960
```

**Perf caveat — pure_simple is interpreter + canvas bound.** Two O(n²) traps
(fixed 2026-06-06, see the bug doc): a heuristic-surface `push`-loop buffer build
(use `[0; w*h]` array-repeat), and the in-place array-write fix (`2d4579a0`) must
be in the **running binary** — a stale `bin/simple` (built before that fix) clones
the whole framebuffer on every pixel write → O(n²) (e.g. 192s vs 15s at 320×240).
If headless web render is pathologically slow, suspect a stale deployed driver;
rebuild it (`cargo build --release -p simple-driver` + redeploy, or
`bootstrap-from-scratch.sh --deploy`). Keep pure_simple viewports ≤ ~400 wide.

## Launch (on-screen, macOS)

```bash
scripts/gui/macos-gui-run.shs <app.spl> [args...]
# wraps the GUI driver in a throwaway .app so the window-server registers it
```

## Capture & verify the FRAMEBUFFER (absolute oracle)

The ground truth is `read_pixels()` dumped to a PPM — it proves the lane renders
independent of window-server/compositor/permission state. Screen capture by
region is flaky (it can grab whatever window sits at those coordinates).

Each app dumps `read_pixels()` → P6 PPM when its env var is set:

```bash
# 2D shapes
SHAPES_PPM=/tmp/shapes.ppm   SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src \
  src/compiler_rust/target/gui/debug/simple run examples/06_io/ui/engine2d_shapes_gui.spl
# GUI widgets
SHOWCASE_PPM=/tmp/widgets.ppm SIMPLE_EXECUTION_MODE=interpret SIMPLE_LIB=src \
  src/compiler_rust/target/gui/debug/simple run examples/06_io/ui/widget_showcase_gui.spl
# Web/HTML at a realistic size (binary P6 via encode_ppm_p6)
PAGE_W=440 PAGE_H=360 SIMPLE_EXECUTION_MODE=interpret SIMPLE_TIMEOUT_SECONDS=1200 SIMPLE_LIB=src \
  src/compiler_rust/target/gui/debug/simple run \
  examples/06_io/ui/web_render_page_ppm.spl <file.html> /tmp/out.ppm
```

Always set **`SIMPLE_EXECUTION_MODE=interpret`** for these graphics apps: in default
JIT mode the cranelift JIT panics resolving the winit/engine2d runtime externs
(`rt_winit_event_loop_new`; the rt_* handle-table split). `--mode=interpreter` is
**not** sufficient — JIT is still attempted; the env var is what the driver honors
(macos-gui-run.shs sets it). Use `encode_ppm_p6(w,h,pixels)` (`common.image.ppm_decode`) — it
  pre-sizes + index-assigns (O(n)); never the O(n²) ASCII-P3 `ppm = ppm + …`
  concat, and never `expr as u8` in an element store (the `[u8]`→extern marshalling
  drops u8-tagged elements — store masked ints). The web layout lane is
  interpreter-bound (~1.5 ms/px): a 440×360 page ≈ a few minutes.

## Bit-level backend parity gates (numeric oracle)

```bash
# CPU-NEON vs Metal GPU, all primitives bit-exact (gpu_ok=true means real GPU)
SIMPLE_BIN="$PWD/src/compiler_rust/target/gui/debug/simple" SIMPLE_LIB="$PWD/src" \
  bash scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
# CPU-NEON vs scalar bit-exact + NEON actually engaged (native_simd_hits>0)
SIMPLE_BIN="$PWD/src/compiler_rust/target/gui/debug/simple" SIMPLE_LIB="$PWD/src" \
  bash scripts/check/check-cpu-simd-engine2d-evidence.shs
```

## Mac RenderDoc + Vulkan GUI/Web/2D Gate

Use the setup wrapper as the canonical entrypoint. macOS is the current
top-level actual-run workflow. Windows and Linux are deferred until separate
platform runbooks produce matching evidence keys and gates.

First prove the host Vulkan stack:

```bash
brew install vulkan-tools vulkan-loader vulkan-headers molten-vk spirv-tools glslang
vulkaninfo --summary  # must show the Apple GPU through MoltenVK
scripts/setup/setup-gui-web-2d-vulkan-env.shs --check
```

Then collect the Simple RenderDoc/Vulkan debug lane and the production parity
lane:

```bash
scripts/setup/setup-gui-web-2d-vulkan-env.shs --run

SIMPLE_BIN=src/compiler_rust/target/release/simple \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --renderdoc-simple

SIMPLE_VULKAN_READBACK_WORK_DIR=build/renderdoc/simple-vulkan-readback \
SIMPLE_LIB=src \
  sh scripts/check/check-vulkan-engine2d-readback.shs

sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
sh scripts/check/check-gui-renderdoc-feature-coverage-status.shs
```

On a prepared RenderDoc host, `scripts/setup/setup-gui-web-2d-vulkan-env.shs
--renderdoc-simple` is the supported macOS Simple debug path. The all-lane
`--renderdoc` mode is for cross-surface evidence collection and should treat
macOS Chrome/Electron captures as exploratory unless Chromium logs prove Vulkan
and the RDOC gates pass. Do not report Windows or Linux status from this Mac
runbook.

Vulkan browser proof requires more than `--use-angle=vulkan`. If Chrome or
Electron writes a bitmap but logs `angle=vulkan` as unavailable, record
`vulkan-angle-unavailable` and keep the Chromium lane failed. The Simple 2D lane
must prove Vulkan via the Simple Vulkan/Engine2D readback or RenderDoc gate; a
spec that skips hardware assertions when `probe_vulkan()` fails is not enough.

For 8K GUI/web/2D performance claims, keep a retained row in `doc/09_report` or
`doc/10_metrics` with viewport, backend, binary/source revision, readback mode,
p50/p95, RSS or memory, fallback state, and checksum/readback proof; otherwise
record an explicit blocker. For Metal claims, only macOS native raw Metal
readback with backend handle and checksum/readback provenance is proof; other
hosts report `metal-requires-macos`.

## Mobile (Tauri Android / iOS) sanity

The mobile GUI lane runs the **real** `render_html_tree` + `generate_css`
pipeline as a subprocess inside the Tauri v2 shell (`tools/tauri-shell`), driven
by a bundled `.ui.sdn`. **Same source both platforms; only build config + the
cross-compiled runtime differ.** Full guide:
`doc/07_guide/platform/mobile/tauri_mobile_guide.md` (§1b live source-bundle).

Rebuild loop after changing UI source (`src/app/ui*`, `html_widgets.spl`, a
`.ui.sdn`): regenerate the embedded bundle, then the app.

```bash
sh tools/tauri-shell/scripts/build-ui-bundle.shs          # → ui_bundle.tar.gz (~8 MB, gitignored)
cd tools/tauri-shell/src-tauri
cargo tauri android build --target aarch64 --debug        # Android APK
cargo tauri ios build --debug --target aarch64-sim        # iOS simulator (.app)
```

Pre-flight oracle (desktop, no device): extract the bundle exactly as the device
will and run the genuine entry — proves the bundle is self-sufficient + the
renderers fire, via grep on the emitted HTML (not interpreter `index_of`):

```bash
printf '{"type":"quit"}\n' | bin/simple run src/app/ui/main.spl tauri \
  examples/06_io/ui/widget_showcase_mobile.ui.sdn 2>/dev/null \
  | grep -oE 'widget-[a-z-]+' | sort -u    # every supported kind must appear
```

On-device verification (absolute oracles, NOT `eval OK` which ≠ painted):
- **Render:** logcat / os_log `[tauri-shell] render, html_len=<N>` + a real
  screenshot showing styled widgets (`adb exec-out screencap` / `xcrun simctl io
  booted screenshot`). A blank webview with `eval OK` is the iOS ATS/scheme bug.
- **Events:** clear the log, inject a REAL tap on a **state-changing** control
  (a tab/checkbox — `OK`/nav actions may not re-render), then confirm a NEW
  `html_len` render line appeared (the subprocess re-rendered in response) and
  the screenshot shows the state change. `adb shell input tap X Y`; on the iOS
  sim use computer-use pixel clicks (simctl has no tap). Tapping plain widget
  text can select it instead of clicking — aim at buttons/tab cells.
- Same `.ui.sdn` → byte-identical `html_len` on both platforms = same source.

## Gotchas

- `bin/simple run` enforces a 10s example watchdog (wall-clock + RSS). Override
  with `SIMPLE_TIMEOUT_SECONDS=<n>` (0 disables). The web-layout lane is
  interpreter-bound (~1.5 ms/px) — keep web sanity surfaces ≤ ~900×760.
- Engine2D/Metal/winit runtime externs live in the **GUI driver**
  (`src/compiler_rust/target/gui/debug/simple`), not the stale `bin/release`.
- Reference: `doc/04_architecture/ui/simple_gui_stack.md` → "GUI Sanity Apps".
