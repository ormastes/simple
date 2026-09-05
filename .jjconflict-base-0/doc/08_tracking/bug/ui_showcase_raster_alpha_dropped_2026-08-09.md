# ui_showcase 2D/gui hosts wrote translucent fills opaque — rows washed out to solid white

- **ID:** ui_showcase_raster_alpha_dropped_2026-08-09
- **Status:** FIXED 2026-08-09
- **Found by:** computer-use capture sweep (2D PPM vs web HTML render), 2026-08-09
- **Area:** `src/app/ui_showcase/hosts/scene_raster.spl`
- **Severity:** medium — the 2D showcase capture rendered the glass theme's
  translucent row overlays as solid white blocks, hiding the white row label
  text; the web host (CSS rgba composited by the browser) rendered the same
  scene correctly, so the hosts visibly disagreed

## Symptom

`SIMPLE_SHOWCASE_CAPTURE=build/showcase/2d.ppm simple run
src/app/ui_showcase/hosts/main_2d.spl`: the list area came out pure
`#ffffff` (probe pixels (30,10),(160,30),(200,45) all 255,255,255) while
the lower panel was the correct dark `#1e1e23`. The scene paints row
overlays at ~6% alpha white (`rgba(255,255,255,0.058)` in the web host's
CSS output) over the dark ground; the 2D raster turned them opaque.

## Root cause

`RasterSurface.put` stored the raw ARGB word and dropped alpha — a
deliberate scope cut ("no alpha blending (fills are written opaque)") from
the original capture-harness pass, which only needed "nonblank / >= 2
distinct pixel values". Visually wrong for any translucent fill.

## Fix

`put` now does source-over blending over the opaque ground
(`out = (src*a + dst*(255-a) + 127) / 255` per channel, result alpha 255),
short-circuiting a==0 (skip) and a==255 (plain store). Header scope comment
updated. `raster_to_ppm_bytes` is unchanged (still drops alpha on export,
now correct because pixels are pre-composited).

## Verification

Re-ran the 2D host capture; list rows render dark with visible labels,
matching the web host's Chrome screenshot of the same scene
(`build/showcase/web.html`).

## Related

- Theme snapshot drift fixed same session: regenerated
  `src/lib/common/ui/generated/aetheric_dark_theme_snapshot.spl` via
  `simple theme-sync compile-to-spl --theme=aetheric_dark` (source manifest
  sha had drifted; material hash/CSS identical). `theme_package_spec` 16/16,
  `theme_render_snapshot_spec` 1/1.
