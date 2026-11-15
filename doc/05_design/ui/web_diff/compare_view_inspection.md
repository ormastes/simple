# Compare-view inspection (2026-11-14)

Lets a person look at the two pixel buffers a comparison test is diffing:
Simple 2D vs Skia, and Simple web vs Chrome.

## Option

| Env | Values | Default |
|---|---|---|
| `SIMPLE_COMPARE_VIEW` | `off` — nothing opens; `auto` — open, then close by itself; `stay` — open and leave open | `off` |
| `SIMPLE_COMPARE_VIEW_MS` | auto-close delay in ms | `3000` |
| `SIMPLE_COMPARE_VIEW_SCREEN` | `WxH` host work-area override | probed |
| `SIMPLE_COMPARE_VIEW_BROWSER` | viewer executable (Chromium family) | Chrome, then Edge/Chromium |

```bash
SIMPLE_COMPARE_VIEW=stay bin/simple test test/03_system/gui/pixel_compare/chromium_vs_simple_text_spec.spl
```

Off costs one environment read per comparison.

## Layout rule

1. Both images fit the host screen next to each other -> **side by side**.
2. Else -> **one image per tab**.
3. One image alone does not fit -> **fit to window** (default), or untick it
   for **scrollbars** at 1:1.

The window is sized to the content and never larger than the host work area.
If the screen size cannot be probed the viewer starts maximized. The page
re-applies rule 1-3 with CSS media queries, so it stays right when resized.

## Pieces

| File | Role |
|---|---|
| `src/lib/common/ui/compare_view.spl` | pure: option parse, window plan, page HTML, viewer args, RGBA8->ARGB |
| `src/lib/nogc_sync_mut/ui/compare_view_host.spl` | effects: write `build/compare_view/<name>/{a.png,b.png,index.html}`, probe screen, find and launch viewer |
| `test/01_unit/lib/common/ui/compare_view_spec.spl` | plan / page / args (written first) |
| `test/01_unit/lib/nogc_sync_mut/ui/compare_view_host_spec.spl` | off = no artifacts; on = artifacts; never opens a window |

Tests call `compare_view_inspect(name, label_a, argb_a, w, h, label_b, argb_b, w, h)`
(or `compare_view_inspect_rgba8` for byte buffers). Convention: A = Simple,
B = the reference (Skia / Chrome). The return value is a status text
(`off`, `open:<page>`, `closed:<page>`, `no-viewer:<page>`, ...); a viewer
problem never fails the test.

## Why a Chromium app window, not a native Simple window

Measured on the deployed binary, 2026-11-14:

- `rt_sdl2_present_rgba` is native-link only; the interpreter's SDL2
  satellite cannot present pixels (`scripts/build/build_simple_runtime_sdl2.shs`
  header), and specs run on the interpreter.
- `rt_winit_*` is behind the seed's `gui` cargo feature, off in the deployed
  binary (`unknown extern function: rt_winit_event_loop_new`).

A script-free page gets tabs (radio inputs), fit (checkbox), and scrollbars
(`overflow:auto`) from the platform. The plan and artifacts are independent of
the launcher, so a native window can replace `_cv_launch_detached` later
without touching callers.

`stay` must not let the viewer inherit the test's stdout: a direct spawn and
`cmd /c start` both did, and a piped test run hung until the window was
closed. Windows uses `Start-Process` (ShellExecute inherits no handles);
POSIX uses `nohup ... >/dev/null 2>&1 &`. Only the Windows path has been run.

## Migrated comparison sites

| Lane | Site |
|---|---|
| Skia vs Simple 2D | `src/app/test/vulkan_2d_qualification/candidate_receipts.spl` (engine vs upstream Skia capture) |
| Skia reftest | `test/03_system/gui/reftest/parity/pixel_diff.spl` `compare_pictures` |
| Chrome vs Simple web | `test/03_system/gui/pixel_compare/chromium_vs_simple_text_spec.spl` |
| Chrome vs Simple web | `src/app/ui/chrome_showcase/pixel_diff.spl` `compare_pair` (catalog) |
| Chrome vs Simple web | `src/app/wm_compare/_HtmlCompat/report_and_fixture.spl` (html compat) |
| Chrome vs Simple web | `src/app/wm_compare/site_corpus_compat.spl` (famous-site corpus) |
| 2D backends | `src/app/wm_compare/graphical_backend_equality.spl`, `_WmCompareMain/capture_io.spl` |

## Not done

- No diff-highlight third image.
- No `bin/simple test --compare-view` flag; the environment variable is the option.
- macOS screen probe (falls back to maximized).
- PNG encoding runs on the interpreter; very large buffers are slow when the option is on.
