# SimpleOS WM text: broken font fallback and missing placeholder degrade when metrics invalid

**Date:** 2026-07-17
**Status:** fixed / landed (SHAs below)
**Severity:** P2 — WM text rendered unreadably (or faulted) when the real font
was unavailable or its metrics were invalid, with no readable fallback.
**Component:** SimpleOS WM text path — `src/lib/common/ui/window_scene_draw_ir.spl`,
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`.

## Symptom

On the SimpleOS baremetal WM:

- when the real font could not be loaded, the WM font fallback rendered
  unreadable text rather than a legible fallback;
- when font metrics were invalid, WM text had no safe degrade and could produce
  garbage or a fault instead of a placeholder;
- shared renderer state was not synchronized, so the fallback/degrade decisions
  read stale state.

## Root cause

Missing/incorrect degrade policy in the WM text path: no readable font fallback
when the primary font is unavailable, no placeholder path when metrics are
invalid, and unsynchronized shared renderer state feeding those decisions.

## Fixing commits

- `2ccde7e42f9` fix(simpleos): restore readable WM font fallback
- `d9d4a9eb6e2` fix(lib/ui): WM text degrades to placeholder bar-rect when font
  metrics invalid (baremetal)
- `d42f2c35b21` fix(fonts): synchronize shared renderer state

## Affected files

- `src/lib/common/ui/window_scene_draw_ir.spl`
- `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`

## Related

- `baremetal_rt_file_read_bytes_halts_no_vfs_2026-07-17.md` — the empty-read
  degrade that triggers this fallback.
- `self_hosted_font_renderer_optional_field_shape_2026-07-11.md` — the shared
  `FontRenderer` state-retention concern that the renderer-state sync addresses.
