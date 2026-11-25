# Caret Suite & ClockApp Multi-App A2UI Integration Manual

**Source Spec:** `test/02_integration/app/a2ui_caret_and_clock_spec.spl`  
**Requirements:** `REQ-A2UI-004`, `REQ-A2UI-009`, `REQ-A2UI-011`, `REQ-A2UI-012`

## Primary Scenarios

1. **Caret Metric Sentinels, Terminal Sanitization, & CLI Routing (`REQ-A2UI-009`)**
   - Verify `-1` CPU/RSS sentinels stay `"CPU unavailable"` / `"memory unavailable"` while `0` renders `"CPU 0%"` / `"0 MB"`.
   - Strip ANSI CSI escape codes from terminal pane text so output renders as inert text.
   - Resolve `--a2ui` and `--a2ui-json` via `cs_resolve_ui_mode`.

2. **Side-by-Side Caret & ClockApp Isolation (`REQ-A2UI-004`, `REQ-A2UI-012`)**
   - Mount Caret Suite and SimpleOS `ClockApp` (using zero Caret imports) onto one shared `A2uiSurfaceRegistry` with colliding `root`, `refresh`, and `main` wire IDs.

3. **CaretA2uiHost Live Sync & Handler Hot Swap (`REQ-A2UI-009`, `REQ-A2UI-011`)**
   - Initialize `CaretA2uiHost`, edit `/draft/body`, sync `CsDashboard` into an A2UI `UITree`, and hot-swap handler generation (`caret_handler_abi_v1`) without dropping active drafts or surfaces.
