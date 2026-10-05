# GUI showcase window: glyphs break up, and there is no HiDPI scale

- **Filed:** 2026-10-05
- **Area:** `src/app/ui_showcase/hosts/host_gui.spl` (`ScreenGuiHost`),
  `src/app/ui_showcase/hosts/scene_raster.spl` (`RasterSurface`),
  `src/lib/nogc_sync_mut/ui/gui_renderer.spl`
- **Status:** FIXED 2026-10-05

## Symptom

`SIMPLE_GUI=1 SIMPLE_SHOWCASE_W=3840 SIMPLE_SHOWCASE_H=2160 ... main_gui.spl`
opened a real window. In it, "Line 2" showed as `L·· 2` and "Item" as `I··`:
strokes were missing. The UI also filled only part of the window.

## Root cause

This is not a JIT defect. The JIT and the interpreter rasterize byte-identical
frames (640x400 `cmp`). At 3840x2160 the rasterized frame is crisp.

1. **Frame/drawable mismatch (the broken glyphs).** `ScreenGuiHost` rendered
   at the REQUESTED size (3840x2160). The window's actual drawable was
   1920x1062: winit reports `scale_factor_milli=1000` on the display the
   window opened on, and the OS clamps the window to that screen.
   `rt_winit_window_present_staged` then nearest-samples the 3840-wide staging
   frame into the 1920-wide surface (`sx = dx * src_w / dst_w`). That drops
   every other column and row, so the 1-px strokes of the 5x7 font break up.
   This is pre-existing on `main` and independent of #2527.
2. **No device scale.** The scene was always laid out 1 logical px = 1 device
   px, so a 2x backing store would show the UI at half size.

## Fix

- `ScreenGuiHost` sizes its frame from `GuiRenderer.inner_size()`, the actual
  drawable. The provider never resamples, so no strokes are dropped.
- Device scale:
  - Source: `SIMPLE_GUI_SCALE` (a positive integer) if set, otherwise the window's `rt_winit_window_scale_factor_milli` rounded to an integer, otherwise 1.
  - `size()` reports LOGICAL extents (device / scale).
  - The scene is rasterized with `raster_scene_argb_scaled`: `RasterSurface.scale` multiplies rects and clips, glyph cells cover s x s device pixels, and path strokes are drawn at device resolution.
  - Pointer and resize events are divided back to logical units. Wheel notches are left unchanged.
- Startup prints `showcase gui: device=WxH scale=S (window
  scale_factor_milli=M) logical=WxH`, so the scale in use is visible.
- ponytail: fractional factors (1.25, 1.5) round to an integer scale. The
  upgrade is a fixed-point scale in `RasterSurface`.

## Evidence

- A scale-1 raster is byte-identical before and after (640x400 `cmp`).
- Logical 1920x1080 rendered at 2x into 3840x2160 reads cleanly when
  downsampled to a 1280-wide thumbnail.
- Real window on this host: `device=1920x1062 scale=1 (window
  scale_factor_milli=1000) logical=1920x1062`, `frames=3`.
- Spec: `test/01_unit/app/ui_showcase/host_gui_device_scale_spec.spl` (4/4):
  - 2x rect and glyph map exactly to 2x2 blocks of the 1x surface;
  - scale resolution from milli values and overrides;
  - pointer events are divided, wheel notches are not.
