# Interactive Browser Window Event Routing (`simple browser`)

> Traceability: `REQ-WEB-005`, `REQ-WEB-007` — Pointer hit-testing (`<a href>` / `<button>` / hover), clamped `scroll_y` wheel & scroll rendering, keyboard history/reload/close routing, and preservation of the `gui_window.spl` render-free JIT call boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

## Scenarios

- **AC-1**: Clicking `<a href>` resolves relative URLs against the active URL, appends history, and resets `scroll_y` to `0`.
- **AC-2**: Hover tracks target keys and clicking `<button>` dispatches a button action status without navigating away.
- **AC-3**: Wheel deltas clamp `scroll_y` into `[0, max_scroll_y]` and scrolled Engine2D output reflects document offset (`#112233` anchor scrolls past viewport).
- **AC-4**: Keyboard shortcuts route `Down`/`Up`/`Home`/`End`, `Left`/`Backspace` (Back), `Right` (Forward), `R`/`F5` (Reload), and `Escape` (Close).
- **AC-5**: `src/app/browser/gui_window.spl` stays decoupled from `browser_engine`, `render_adapter`, and `render_lane`.
