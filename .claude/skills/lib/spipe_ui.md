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

## Launch (on-screen, macOS)

```bash
scripts/gui/macos-gui-run.shs <app.spl> [args...]
# wraps the GUI driver in a throwaway .app so the window-server registers it
```

## Capture & verify the FRAMEBUFFER (absolute oracle)

The ground truth is `read_pixels()` dumped to a PPM — it proves the lane renders
independent of window-server/compositor/permission state. Screen capture by
region is flaky (it can grab whatever window sits at those coordinates).

- 2D + widgets: dump via the app's `read_pixels()` → P6 PPM.
- Widgets headless dump: `SHOWCASE_PPM=/tmp/widgets.ppm … run
  examples/06_io/ui/widget_showcase_gui.spl --mode=interpreter`.
- Web/HTML headless dump at a realistic size (binary P6 via `encode_ppm_p6`):
  ```bash
  PAGE_W=440 PAGE_H=360 SIMPLE_TIMEOUT_SECONDS=1200 SIMPLE_LIB=src \
    src/compiler_rust/target/gui/debug/simple run \
    examples/06_io/ui/web_render_page_ppm.spl <file.html> /tmp/out.ppm --mode=interpreter
  ```
  Always pass **`--mode=interpreter`** for these graphics apps: default JIT mode
  panics resolving the winit/engine2d runtime externs (`rt_winit_event_loop_new`;
  the rt_* handle-table split). The macos-gui-run.shs launcher already forces
  interpret mode. Use `encode_ppm_p6(w,h,pixels)` (`common.image.ppm_decode`) — it
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

## Gotchas

- `bin/simple run` enforces a 10s example watchdog (wall-clock + RSS). Override
  with `SIMPLE_TIMEOUT_SECONDS=<n>` (0 disables). The web-layout lane is
  interpreter-bound (~1.5 ms/px) — keep web sanity surfaces ≤ ~900×760.
- Engine2D/Metal/winit runtime externs live in the **GUI driver**
  (`src/compiler_rust/target/gui/debug/simple`), not the stale `bin/release`.
- Reference: `doc/04_architecture/ui/simple_gui_stack.md` → "GUI Sanity Apps".
