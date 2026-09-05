# ui_showcase 2D raster dropped GROUP offsets/clips — scroll content spilled over the whole frame

- **ID:** ui_showcase_2d_raster_group_clip_dropped_2026-08-09
- **Status:** FIXED 2026-08-09
- **Found by:** computer-use 3D/web/2D showcase sweep, 2026-08-09 (small-surface
  pixel probe at 240x180: scroll rows rendered on top of the menubar and every
  panel below their viewport)
- **Area:** `src/app/ui_showcase/hosts/scene_raster.spl`
- **Severity:** high for the 2D capture lane — any scroll batch rendered its
  full content at group-LOCAL coordinates with no clip, so rows painted over
  the toolbar, sibling panel, windows row and probe pane

## Symptom

A 240x180 probe render of the showcase scene showed `L row 0` glyphs
overlapping the menubar text, rows 4+ spilling down over `alpha`/`beta`, the
probe labels and the statusbar, and the right panel's rows stacked on the left
panel's. The web host (`host_web.spl`) rendered the same scene correctly
because it expands GROUP commands into offset/clip wrapper divs.

## Root cause

HEAD's `raster_scene_into` skipped GROUP commands entirely: no transform
dx/dy was applied to children (authored in group-local coordinates, so they
landed near the origin) and no clip was enforced (so the full scroll content
painted instead of the viewport slice). `RasterSurface` also had no `clear`
method even though `host_2d.spl`'s per-frame reset calls
`surface.clear(RASTER_BG)` — a latent compile break of the 2D entry against
this raster (`error: semantic: method 'clear' not found on type
'RasterSurface'`).

## Fix

- `raster_scene_into` now runs the same open-group cursor as the web host: a
  GROUP's transform dx/dy is added to every child command whose `parent_id`
  matches the group's `component_id`; a GROUP with a clip rect constrains its
  children's pixels to `(dx+clip.x, dy+clip.y, clip.w, clip.h)`. Cursor resets
  when the walk leaves the group's children. The v2->v3 adapter never nests
  groups, so one cursor suffices.
- `RasterSurface` gained `clip_x/clip_y/clip_w/clip_h` (default: full
  surface), `set_clip`/`clear_clip`, and the missing `clear(bg)` per-frame
  reset (pixels + clip). `put` rejects pixels outside the active clip.
- Header scope comment updated (group offsets/clips are now honoured).

## Verification

- 240x180 probe PPM: menubar items spread and unobscured, scroll rows clipped
  mid-glyph at the viewport edge, no spill into lower panels.
- Pixel oracle (`showcase_build` + `raster_scene_into` at 240x180): menubar
  band painted, >= 5 separated light runs across the bar (items spread),
  statusbar band + text present — all PASS.
- Re-capture: `SIMPLE_SHOWCASE_CAPTURE=build/showcase/2d_final.ppm
  <simple> run src/app/ui_showcase/hosts/main_2d.spl` (320x240, 3 frames).

## Related

- `ui_showcase_raster_alpha_dropped_2026-08-09` (same file, alpha blending).
- `seed_flat_namespace_trait_struct_collision_2026-08-09` (same sweep).
