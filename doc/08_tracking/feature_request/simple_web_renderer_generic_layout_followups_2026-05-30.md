# Simple Web Renderer — generic-HTML real-layout follow-ups

Filed-on: 2026-05-30
Filed-by: claude (web-renderer session)
Target: `src/lib/gc_async_mut/gpu/browser_engine/`

## Context

As of `main` (`chore: sync ui renderer and tauri generated updates`), the
production entry `simple_web_engine2d_render_html_pixels(...)` in
`simple_web_engine2d_renderer.spl` no longer greps every page: HTML the
substring heuristic does **not** recognize is routed to a real
parse → CSS cascade → block layout → paint engine
(`simple_web_html_layout_renderer.spl`, `simple_web_layout_render_html_pixels`).
The heuristic branches are retained only for the contract/corpus fixtures whose
exact pixels the test suite pins (resolved background color, first-block color,
famous-site corpus, `wm-app-titlebar`/`wm-app-content` chrome, the
`Simple Web`/`about:network` mark).

Existing fixture specs stay green because every pinned fixture still matches the
heuristic discriminator and routes to the old path. The items below are the
work that is genuinely *not yet done* — recorded here so it is not silently
dropped. None of these block the current green test state.

## Open Requests

### FR-WEBRENDER-001 — Generic-HTML layout render speed under the interpreter

- **Filed-on:** 2026-05-30
- **Filed-by:** claude (web-renderer session)
- **Target:** `simple_web_html_layout_renderer.spl`
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  The real layout renderer paints text glyph-by-glyph; a realistic full page
  (`examples/ui/sample_page.html`, ~4 KB) renders in ~2m37s under
  `SIMPLE_EXECUTION_MODE=interpret`. That is correct but far too slow for any
  interactive or test-harness use. Want either (a) a lean direct-`[u32]`
  framebuffer text rasterizer (bitmap font blit, no per-pixel engine dispatch)
  so a full page renders in single-digit seconds under the interpreter, or
  (b) a working `native-build` of the renderer so it runs compiled. Note:
  `native-build` currently exits 3 with no diagnostic in this checkout (see
  Notes) — option (a) is the unblocked path.
- **Acceptance-criteria:**
  - [ ] `examples/ui/sample_page.html` renders through the layout renderer in
        < 10s under `SIMPLE_EXECUTION_MODE=interpret` on the dev machine.
  - [ ] ASCII preview / pixel output still shows legible text rows and block
        backgrounds (no fidelity regression vs the current path).
- **Related-upfront:** `doc/03_plan/simple_web_renderer_completion_audit.md`
- **Related-design-doc:** tbd
- **Notes:** `bin/simple native-build` exits 3 with empty stdout/stderr for
  every entry tried (including `examples/01_getting_started/hello_native.spl`)
  across the bootstrap and release binaries; the bootstrap binary also panics
  on no-args (`rt_ptr_read_i64`). Native-build appears environmentally broken in
  this checkout — repairing it (bootstrap rebuild) is its own task and is the
  precondition for option (b).

### FR-WEBRENDER-002 — Pixel-level test coverage for the generic layout path

- **Filed-on:** 2026-05-30
- **Filed-by:** claude (web-renderer session)
- **Target:** `test/unit/lib/gc_async_mut/gpu/browser_engine/`
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  The new generic-HTML branch (`simple_web_layout_render_html_pixels`) is only
  exercised indirectly. Add a focused spec that feeds generic document HTML
  (heading + paragraph + a colored block, none of the heuristic markers) and
  asserts: the page background is painted, the block background appears at its
  laid-out box, and text rows produce non-background ink at expected rows. Keep
  assertions structural (region has ink / block color present) rather than
  pinning every pixel, so the layout engine can improve without churn.
- **Acceptance-criteria:**
  - [ ] A spec drives `simple_web_engine2d_render_html_pixels` with marker-free
        generic HTML and confirms it took the real-layout branch (distinct
        multi-color output, not a flat fill).
  - [ ] Spec passes under `--mode=interpreter --clean` within the suite's
        watchdog budget.
- **Related-upfront:** `doc/03_plan/simple_web_renderer_completion_audit.md`
- **Related-design-doc:** tbd
- **Notes:** Must not pin the famous-site corpus pixels — those stay on the
  heuristic. Generic-HTML assertions only.

### FR-WEBRENDER-003 — Chrome-compatible text antialiasing / CSS coverage

- **Filed-on:** 2026-05-30
- **Filed-by:** claude (web-renderer session)
- **Target:** `simple_web_html_layout_renderer.spl` + `browser_renderer.spl`
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  The real layout renderer covers block flow, the CSS cascade for color /
  background / font-size / text-align / padding / margin, and word-wrapped
  text. It does not implement Chrome-compatible glyph antialiasing, LCD
  subpixel/gamma compositing, inline flow (multiple inline boxes on a line),
  fl/grid layout, or borders. Full corpus parity remains the long-standing open
  goal tracked in the completion audit; this FR is the umbrella pointer for that
  remaining renderer work so it is visible from the tracker.
- **Acceptance-criteria:**
  - [ ] Linked to a concrete plan slice before being marked Accepted.
- **Related-upfront:** `doc/03_plan/simple_web_renderer_completion_audit.md`
- **Related-design-doc:** `doc/08_tracking/bug/simple_web_renderer_ttf_glyph_metrics.md`
- **Notes:** Umbrella entry — the audit doc holds the detailed, experiment-by-
  experiment history of rejected scalar-alpha attempts. Do not re-litigate those
  here.
