# Software web-render oracle silently blanks text when its wall-clock budget is exhausted

- **Status:** open
- **Filed:** 2026-08-04
- **Component:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
- **Severity:** high — it makes the software oracle unusable as a comparison
  reference on a loaded host, and it fails *silently* (no error, exit 0).

## Symptom

`simple_web_layout_render_html_software_pixels(html, 32, 32)` for
`<p>Text lane</p>` returns a page with **0 inked pixels** instead of the correct
134, intermittently, with no diagnostic. The returned buffer is the right length
(1024) and uniformly background-white, so every length/format check still passes.

## Reproduction

Host load was 32–45 throughout. Same binary, same pristine tree, no source change
between runs — file hashes verified byte-identical to the base commit:

| run | `SIMPLE_WEB_RENDER_BUDGET_MS` | oracle ink |
|-----|-------------------------------|------------|
| 1   | unset (default)               | 134        |
| 2   | unset                         | 134        |
| 3   | unset                         | 0          |
| 4   | unset                         | 0          |
| 5   | unset                         | 0          |
| 6   | unset                         | 134        |
| 7   | unset                         | 134        |
| 8–11| `60000`                       | 134, 134, 134, 134 |

With the budget pinned large the result is stable across every run; unpinned it
flaps. The Draw IR lane (`simple_web_render_html_to_pixels_with_engine2d_backend`)
returned 111 in **all** of the above, so this is specific to the software lane.

This was initially and wrongly attributed to `.cache/simple/host/<triple>/cpu_config.sdn`
(deleting it appeared to fix the flap). That was a coincidence of run ordering:
the tracked blob and the on-disk file are byte-identical, and the flap reproduces
with the file present *and* absent. Cache content is not the variable; wall-clock
budget is.

## Mechanism

The software renderer partitions one wall-clock budget across layout/paint stages
via `_web_budget_begin` / `_web_budget_rearm`
(`simple_web_html_layout_renderer.spl:1751,1792,1864,1949`), with the default from
`WEB_RENDER_BUDGET_MS` and an override read from `SIMPLE_WEB_RENDER_BUDGET_MS`
(`simple_web_html_layout_renderer_foundation.spl:126-133`).

When the budget expires before the text-paint stage runs, that stage is skipped
and the already-allocated white framebuffer is returned as if it were a complete
render. There is no "degraded"/"truncated" flag on the returned `[u32]`, so a
caller cannot tell a budget-starved blank page from a legitimately empty one.

## Why it matters

Any spec that compares a second lane against this oracle is load-flaky by
construction. This is the most likely reason the byte-exactness assertion added
in `3b86328c925` could not simply be restored: even with a correct renderer, the
reference itself intermittently returns a blank page.

## Workaround in place

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl`
passes an explicit large `budget_ms` (`_oracle_budget_ms() = 60000`) to every
oracle call, and its `_raster_family` helper reports `"blank"` — a distinct,
loud verdict — if the oracle degrades anyway.

## Suggested fix

Return the degradation in-band rather than silently: either surface the existing
`SimpleWebLayoutPixelResult` "budget exhausted" state through the `_pixels`
convenience wrappers, or have the wrappers fail loudly when the paint stage was
skipped. A silently-blank framebuffer should never be indistinguishable from a
successful render.
