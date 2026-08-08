# Simple Browser CLI (`src/app/browser/`)

Hosted `app.ui.render`-contract browser app. Renders a page through the real
DOM/CSS/layout/paint engine (`render_html_to_pixel_array`) and reports a
render receipt ("Rendered by Simple Browser engine: 64x36px, N pixels
painted") so output is provably engine-backed, not a placeholder.

## Usage

```bash
bin/simple run src/app/browser/main.spl                # text mode
bin/simple run src/app/browser/main.spl --log-mode=json # HTML-in-JSON mode
bin/simple run src/app/browser/main.spl --open         # real GUI window
bin/simple run src/app/browser/main.spl --help
```

- Default page: `simple://home` (real Hello World page). Pass a URL as the
  positional argument to override.
- Shared log options (`--log-mode`, `--progress`, ...) follow
  `std.cli.log_modes`, same as sibling apps.

## `--open` (real GUI window)

Opens a real OS window via the `GuiRenderer` winit facade
(`src/lib/nogc_sync_mut/ui/gui_renderer.spl`), presents one engine-rendered
frame, and blocks until the window is closed (idle poll sleeps 16ms).

Requirements:
- `build/sffi/libspl_winit.<so|dylib|dll>` — build with
  `scripts/build/build_spl_winit.shs`.
- A reachable display. Linux: X11/Wayland; macOS additionally needs
  `SIMPLE_GUI=1` (winit must run on the main thread).
- Headless verification: run under Xvfb (e.g. a container). Verified recipe
  (2026-08-06): Ubuntu 24.04 + `xvfb imagemagick x11-apps libxkbcommon-x11-0
  libxkbcommon0`, `Xvfb :99`, then
  `DISPLAY=:99 bin/simple run src/app/browser/main.spl --open`; window
  `"Simple Browser - simple://home"` appears in ~60s; screenshot with
  `xwd -id <win> | convert` shows real glyph pixels.

Window/render size is capped at 64x36 (`GUI_WINDOW_WIDTH/HEIGHT` in
`main.spl`) because the engine runs interpreted on this path; see the
ponytail note there before raising it.

## Pitfall: caller-frame silent interpreter fallback

Do NOT move the `browser_engine_pixels_at(...)` call into
`gui_window.spl` (or any module importing extern-heavy modules like
`gui_renderer`): JIT lowering fails silently for that caller frame and the
ENTIRE engine call tree runs tree-walk, ~10-50x slower — a 45-60s render
stops finishing 1800s budgets, with no diagnostic. `main()` renders and
passes ready pixels into `run_browser_window_gui(url, w, h, pixels)` on
purpose. Details and isolation matrix:
`doc/08_tracking/bug/gui_window_caller_frame_silent_interp_fallback_2026-08-06.md`.

## Tests

- `test/01_unit/app/browser/browser_render_adapter_spec.spl` — pure
  dispatch/content logic (engine calls deliberately excluded: one engine
  call alone exceeds the spec runner's 10M-op budget).
- `test/02_integration/app/browser_cli_log_modes_spec.spl` — spawns the real
  CLI (`--help`, `--version`, unknown-option rejection, `--open` parse).

## Related

- Feature expert: `doc/00_llm_process/feature_expert/browser/skill.md`
- Engine internals: `doc/07_guide/ui/browser_engine_implementation.md`
- Don't confuse with `src/app/ui.browser/` (standalone winit widget-tree
  app) or `src/os/apps/simple_browser/` (baremetal).
