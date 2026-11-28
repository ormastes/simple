# Agent Task Breakdown: Simple Web Engine Completion (`release/1.0.0`)

- **Date:** 2026-11-28
- **Target Branch:** `release/1.0.0`
- **Merge Owner:** Foreground Web Engine Lead (interactive with user)
- **Final Reviewer:** Primary model review (`gh pr diff` + `gh pr view --comments` before `gh pr merge --admin --merge`)
- **Sidecar Lanes:** `N/A` for Web Engine (interactive foreground execution; sibling Simple 2D & Simple GUI run in dedicated background worktrees `/Users/ormastes/work/web_2d_gui_2d` and `/Users/ormastes/work/web_2d_gui_gui`)

## Shared Interfaces & Helper Contracts
- **Slice 1 (`REQ-WEB-001`, `REQ-WEB-002`):**
  - `_html_draw_ir_node_paint_order(nodes, styles)` (`paint_layout.spl`)
  - `_paint_passes(...)` (`paint_raster.spl`)
  - `row_flex_item_auto_intrinsic_w(...)` (`layout_engine.spl`)
- **Slice 2 (`REQ-WEB-003`, `REQ-WEB-004`):**
  - `inline_item_width_err_milli(...)`, `form_control_label_width_milli_px(...)` (`layout_foundation.spl`)
  - `flex_row_button_label_at_edge(...)` (`layout_engine.spl`)
- **Slice 3 (`REQ-WEB-005`..`REQ-WEB-008`):**
  - `BrowserWindowAction`, `browser_window_wait(g, w, h)` (`src/app/browser/gui_window.spl`)
  - `browser_open_window(url)` (`src/app/browser/main.spl`)

## Slice Delivery Sequence (Each Merged via PR to `--base release/1.0.0`)
1. **PR 1 (Slice 1):** `REQ-WEB-001` + `REQ-WEB-002` + SSpec tests + manual doc.
2. **PR 2 (Slice 2):** `REQ-WEB-003` + `REQ-WEB-004` + SSpec tests + manual doc.
3. **PR 3 (Slice 3):** `REQ-WEB-005`..`REQ-WEB-008` + interactive `browser --open` SSpec + macOS parity gate evidence.
