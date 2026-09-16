# SIMPLE_WEB_RENDER_BUDGET_MS override silently ignored by stage rearm in the software layout renderer — FIXED

## Status

Fixed. `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`,
`simple_web_layout_render_html_software_pixels` (~line 9334).

## Symptom

Rendering `examples/06_io/ui/browser_common_elements_showcase.html` (a normal
page with headers/paragraphs/sections, routed to the real HTML/CSS layout
engine) at large canvas sizes (empirically, viewport area over roughly
3.7M px, e.g. 2560x1620 or 3840x2160) returned a **uniform, fully-opaque**
pixel buffer — every pixel equal to the page's background color, with no
text, borders, or section boxes painted. `nonzero` == total pixel count (so
it looked "rendered"), but `varied` was false. Setting the documented escape
hatch, `SIMPLE_WEB_RENDER_BUDGET_MS`, to a much larger value (tested up to
300000) had **no effect** — the render still degraded to background-only.

## Root cause

`simple_web_layout_render_html_software_pixels(html, width, height, budget_ms)`
calls `_web_budget_begin(budget_ms)`, which correctly resolves
`SIMPLE_WEB_RENDER_BUDGET_MS` from the environment and arms the global
`_web_render_deadline_us` with the overridden value. But the function then
recomputed a **second, local** `budget_us` straight from the raw `budget_ms`
parameter (the un-overridden default, 10000ms) and used it to `_web_budget_rearm()`
the deadline at the 70%/90%/100% stage boundaries (style → layout → paint).
The very first rearm call (`render_start_us + budget_us * 7 / 10`, i.e. ~7s
from start) clobbered the correctly-overridden deadline back down to the
un-overridden ~7-10s window — so the env override never survived past the
style stage on this entry point. `_traced` and `_at_scroll` sibling entry
points don't call `_web_budget_rearm` and were unaffected.

## Fix

Mirror `_web_budget_begin`'s env-override resolution when computing the
local `budget_us` used for stage rearms, so the override and the global
deadline agree:

```
val env_override = _web_render_budget_ms_env_override()
val resolved_budget_ms = if budget_ms <= 0 or budget_ms == WEB_RENDER_BUDGET_MS:
    if env_override > 0: env_override else: WEB_RENDER_BUDGET_MS
else:
    budget_ms
val budget_us = resolved_budget_ms * 1000
```

This only changes behavior when `SIMPLE_WEB_RENDER_BUDGET_MS` is set in the
environment; with it unset the resolved value is still the 10000ms default,
byte-identical to before for every other caller of this shared engine file
(graphics_2d_showcase_gui.spl, widget_showcase_gui.spl, etc.).

## Verification

`examples/06_io/ui/browser_common_elements_showcase.html` at 3840x2160
(true 4K), `SIMPLE_WEB_RENDER_BUDGET_MS=300000`, bootstrap seed interpreter:
before the fix, uniform/blank (`varied=false`); after the fix,
`nonzero=8294400/8294400`, `varied=true` — full content painted. Wall time
~377s under moderate concurrent system load.

## Area-scaled default budget (landed in the same change)

The engine's default budget (10s) is far too small for large canvases under
the interpreter (a 4K web showcase at 3840x2160 legitimately renders in
~350-590s), so the same edit also floors the default budget to canvas area:

```
val area_floor_ms = (width as i64) * (height as i64) / 16
val default_budget_ms = if area_floor_ms > WEB_RENDER_BUDGET_MS: area_floor_ms else: WEB_RENDER_BUDGET_MS
```

This is monotonic and only ever RAISES the budget above the 10s default (for
canvases larger than ~160k px): any render that finishes under 10s today is
byte-identical, any render that previously degraded-to-blank now gets
proportionally more wall-clock. An explicit caller `budget_ms` or a
shell-exported `SIMPLE_WEB_RENDER_BUDGET_MS` still wins over this floor.

Important: a runtime `env_set("SIMPLE_WEB_RENDER_BUDGET_MS", ...)` from inside
the process does NOT work — the layout renderer (GC-family module) reads the
env via its own `extern fn rt_env_get`, which sees only the real C environ,
while the sync-family `rt_env_set`/`env_set` writes to a separate
interpreter-side overlay that never reaches it. So the env override is a
SHELL-exported escape hatch only; the example apps
(`web_render_file_gui.spl`, `web_standards_showcase_gui.spl`) rely on the
area-scaled default rather than trying (and silently failing) to set the env
var themselves.

Actually shortening the real compute time (e.g. an
`extract_css_vw`/`build_ancestor_clip_cache`/paint-pass optimization for
large canvases) is a separate, larger perf effort and out of scope here.
