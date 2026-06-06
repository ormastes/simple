# SPipe UI Skill — GUI sanity checks (pure-Simple lane)

The pure-Simple GUI lane is verified by **three canonical check apps**, one per
rendering surface. After any GUI / engine2d / web-render change, run all three
and verify the **framebuffer** (not the screenshot — see the oracle rule below).

On macOS the pure-Simple lane = **Engine2D CPU/NEON** (aarch64) + **Metal** (GPU).

## The 3 main GUI check apps

| # | Surface | App | What it must show |
|---|---------|-----|-------------------|
| 1 | **2D rendering** | `examples/06_io/ui/engine2d_shapes_gui.spl` | text, rect (filled/outline), circle, line, gradient, rounded-rect — bit-exact across CPU-NEON and Metal |
| 2 | **GUI widgets** | `examples/06_io/ui/widget_showcase_gui.spl` | the full widget catalog (button, checkbox, radio, input, dropdown, slider, switch, list, table, tree, tabs, progress, card, …) with legible labels |
| 3 | **HTML/web rendering** | `examples/06_io/ui/web_render_file_gui.spl <file.html>` | real HTML+CSS (header/nav, hero, flex two-column main+sidebar, form, footer) via the pure-Simple web layout → Engine2D |

Backend-specific 2D variants (same scene, different backend) for parity work:
`engine2d_cpu_simd_gui.spl` (CPU-NEON) and `engine2d_metal_gui.spl` (Metal).

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
