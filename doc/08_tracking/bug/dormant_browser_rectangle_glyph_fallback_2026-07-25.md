# Dormant browser rectangle-glyph fallback

**Status:** Fixed in source; runtime suite pending a refreshed self-host.

## Symptom

`html_fallback_renderer.spl` contained a second raw-HTML pixel renderer whose
text helper painted one solid rectangle per character instead of emitting
semantic Web/Draw IR text.

## Root cause and fix

The 350-line fallback had no in-tree caller or exported entry point, while the
production browser already uses semantic layout → `DrawIrComposition` →
Engine2D. The smallest safe fix was deletion rather than maintaining a second
HTML/CSS/font pipeline.

## Regression

`legacy_web_gui_wm_font_route_spec.spl` requires the production Draw IR route
and requires this private placeholder source to remain absent.
