---
name: simple_browser
description: Simple Browser app (`src/app/browser/`) — the app.ui.render-contract browser, its render_adapter shape, and its wiring into the WM showcase. Use when adding pages, navigation, or chrome to Simple Browser, or when touching src/app/wm_showcase/session.spl's browser/terminal windows.
---

# Simple Browser

`src/app/browser/` is a hosted app built on the shared `app.ui.render`
contract (`RenderConfig`/`RenderResult` in `src/app/ui.render/types.spl`) —
the same contract ~20 sibling apps use (`src/app/terminal/render_adapter.spl`
is the closest twin; copy its shape for new adapters).

## Files

- `main.spl` — CLI entrypoint (help/version/ready-probe planner, mirrors
  `src/app/terminal/main.spl`).
- `render_adapter.spl` — `render_browser`/`render_browser_html`/
  `render_browser_text`. `render_browser_html(config)` returns a complete
  document via `app.ui.render.html.html_page` (browser chrome — tab strip,
  address bar, nav controls — wrapping the loaded page's own markup).

## Adding a new page

1. Add a case in `browser_page_body_html(url)` and `browser_page_text_lines(url)`
   returning real markup/text for the new URL — never a placeholder string
   standing in for content that doesn't render.
2. If the page needs its own CSS, extend `browser_css()` — real cascaded
   rules, not inline pixel fills.
3. `config.asset_path` carries the URL (see `browser_url(config)`); there is
   no navigation history or multi-tab state yet — one page per render call.

## Three "browser" modules — do not confuse

| Module | Shape | Where it runs |
|---|---|---|
| `src/app/browser/` | `app.ui.render` contract, pure function | Hosted, in-process |
| `src/os/apps/simple_browser/` | `spl_start()` freestanding entry | Boots as a QEMU kernel directly, baremetal only |
| `src/app/ui.browser/` | Standalone winit-windowed app, own event loop | Hosted, but NOT this contract |

Full disambiguation: `doc/00_llm_process/feature_expert/browser/skill.md`.

## Wiring into WM Showcase

`src/app/wm_showcase/session.spl` opens a "Simple Browser" window by calling
`render_browser_html(RenderConfig.html_export()).html_output` and feeding it
through `simple_web_render_html_to_readback_result_with_engine2d_backend` —
the SAME cascade + layout + paint path the GUI/Web showcase windows use.
This is intentional: a showcase window must never render via a pixel
shortcut (a hardcoded rect fill, a fake handle) — see the WM Showcase's own
governing rule at `doc/03_plan/ui/wm_platform_honesty_agent_lanes.md`
("a capability flag must be backed by a real implementation or report
false"). When adding a new showcase window for any app, always route its
content through the app's own real render path, not a synthetic stand-in.

**Cost note:** each HTML-backed showcase window costs 30-50 CPU-minutes to
render in this environment (interpreted cascade+layout+paint). Adding a
window multiplies the full `wm_showcase` spec's wall-clock cost — never run
that spec synchronously inline; dispatch it to a background task/agent.

## Verification

No dedicated `render_adapter_spec.spl` exists yet for this app (parity with
`terminal/render_adapter.spl`, which also has none). The load-bearing gate
today is `test/03_system/gui/wm_showcase_session_capture_spec.spl`'s
byte-identical rect match against the composited desktop — that is what
proves the window actually rendered, not merely that the function returned
without crashing. That gate is currently blocked by an unrelated,
pre-existing defect — see
`doc/08_tracking/bug/wm_showcase_session_capture_spec_no_examples_executed_2026-08-06.md`.
Until that's fixed, verify `render_browser_html`/`render_terminal_html`
directly via a standalone `bin/simple run` probe script instead.

## Shared-working-copy hazard

New, never-committed files in this repo's shared working tree can be
silently reverted by a concurrent session's operation before you get a
chance to commit them (already happened once to this app during
development). Land new work via plumbing CAS promptly rather than leaving
it uncommitted for multiple turns.
