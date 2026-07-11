# browser_engine: `vh` viewport-height units unresolved in margins/lengths

- Status: open
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- Found: 2026-07-11 (example.com render comparison vs Chrome headless)

## Summary
`vh` (viewport-height) units are parsed as raw pixels via `parse_int`, so
`margin: 15vh auto` yields a 15px top margin instead of 15% of the viewport
height. On example.com this leaves the content block ~24px too high compared to
Chrome (Chrome starts the centered block at ~54px = 15vh of 360; the Simple
engine starts it at ~30px). The horizontal centering, `60vw` width, and `1.5em`
heading were fixed in the same session (see below); this is the residual gap.

## Repro (minimal, not site-specific)
```html
<html><body style="margin:0">
  <div style="width:100px;height:20px;margin:40vh auto;background:#3050a0"></div>
</body></html>
```
Render at 200x200 via `simple_web_layout_render_html_software_pixels`. Chrome
places the block's top at y=80 (40vh of 200). The Simple engine places it at
y=40 (40px), because `parse_int("40vh") == 40`.

## Root cause
`apply_decls` resolves `margin`/`margin-*` tokens with `parse_int` /
`margin_token_px`, which honor `%` (negative sentinel) and now `auto`, but drop
the `vh`/`vw` suffix and keep the bare number as px. Only `min-height` currently
special-cases `vh` (via the `min_height_vh` flag). There is no general
viewport-height resolution because `apply_decls` has no access to the viewport
dimensions at style time (it runs before layout).

## Suggested fix
Thread the viewport height (already known at the top-level render entry) into the
margin/length resolution the same way width `%`/`vw` uses a negative sentinel
resolved at layout time — e.g. store `vh` margins as a sentinel and resolve
against `viewport_h` in `layout()` where it is in scope. Mirror the existing
`resolve_horizontal_margin_px` percentage path.

## Related, already fixed this session
- `width: Nvw` was treated as `Npx`; now resolves as a viewport/parent-width
  percentage sentinel (exact for viewport-level elements; nested vw resolves
  against the parent, a documented approximation).
- `font-size: N.Nem` / `rem` / `%` truncated to `parse_int` (`1.5em` -> 1px);
  now resolved against the inherited (em/%) or root (rem) font-size.
- `margin: <len> auto` shorthand ignored `auto`, so horizontal centering never
  applied; the shorthand is now token-aware and layout distributes free space.
