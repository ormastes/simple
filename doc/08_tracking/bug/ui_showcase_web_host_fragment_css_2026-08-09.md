# ui_showcase web host emitted a bare fragment — browser margin shifted the scene, white page washed out the glass theme

- **ID:** ui_showcase_web_host_fragment_css_2026-08-09
- **Status:** FIXED 2026-08-09
- **Found by:** computer-use 3D/web/2D showcase sweep, 2026-08-09 (headless
  Chrome screenshot of `SIMPLE_SHOWCASE_WEB_DOC` output vs the 2D PPM)
- **Area:** `src/app/ui_showcase/hosts/host_web.spl`
- **Severity:** medium — the web host's render visibly disagreed with the
  raster hosts (8px offset, washed-out colors) purely because of the document
  shell, not the scene content

## Symptom

`web_scene_to_html` returned a bare `<div id="showcase-root">` fragment.
Opened directly in a browser:

1. the default 8px body margin shifted the entire scene right/down versus
   the 2D/gui raster hosts, and
2. the glass theme's translucent root surface (`rgba(30,30,35,0.72)`)
   composited over the browser's default WHITE page, washing the whole scene
   out — the raster hosts blend the same alpha over the opaque glass_dark
   ground (`RASTER_BG`, 0xFF141414).

## Fix

The emitted document is now a full shell: `<!DOCTYPE html>` + `<head>` with
`<meta charset>` and a style pinning `html,body{margin:0;padding:0;
background:<RASTER_BG as rgba()>}` — the same opaque ground the 2D host
clears to — so all hosts composite identically and the scene origin is
(0,0). The scene fragment itself is unchanged.

Spec impact: none — `showcase_hosts_spec` asserts `contains("showcase-root")`
etc., all still true. (That spec currently cannot execute: a pre-existing
spec-harness parse failure, `Unexpected token: expected expression, found
RParen`, reproduces on pristine HEAD with both the seed and the stage2
binary; not caused by this change.)

Also corrected a stale comment in `scene_raster.spl`: `RASTER_BG`'s value is
0xFF141414, not the commented 0xFF101214.

## Verification

Headless Chrome screenshot of the regenerated document: scene starts at the
page origin, dark glass palette matches the 2D PPM capture of the same
scene, menubar/statusbar text legible.
