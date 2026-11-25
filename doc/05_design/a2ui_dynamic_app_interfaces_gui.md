# GUI Design Mockup: A2UI Dynamic App Regions & Multi-App Surface Isolation

**Feature:** `a2ui_dynamic_app_interfaces`  
**Design Doc:** [a2ui_dynamic_app_interfaces.md](a2ui_dynamic_app_interfaces.md)

## Multi-App Qualified Surface Isolation

Both Caret Suite (`owner=caret_app:ws1`, `surface=main`) and ClockApp (`owner=clock_app`, `surface=main`) mount into the shared `A2uiSurfaceRegistry` using identical wire component IDs (`root`, `refresh`), separated in native SimpleUI `UITree` nodes by `a2ui:<owner>:<surface>:<gen>:<component>`:

```
+---------------------------------------+  +-----------------------------------+
| Surface: caret_app:ws1 / main (gen 1) |  | Surface: clock_app / main (gen 1) |
| wire root -> a2ui:caret_app%3Aws1:... |  | wire root -> a2ui:clock_app:...   |
| +-----------------------------------+ |  | +-------------------------------+ |
| | workspace: Caret Suite + status   | |  | | main: Clock                   | |
| +-----------------------------------+ |  | |   Stopwatch: 00:01.5          | |
| | roster: search + Refresh + List   | |  | |   Timer:     04:58.5          | |
| |   c_<hex> (k_1_1) -> Agent A      | |  | |   [ Refresh ]                 | |
| +-----------------------------------+ |  | +-------------------------------+ |
| | detail: summary + inert preview   | |  +-----------------------------------+
| +-----------------------------------+ |
| | composer: TextField + Send + out  | |
| +-----------------------------------+ |
+---------------------------------------+
```

## GUI Mode Integration

- `cs_resolve_ui_mode`: supports `--a2ui`, `--a2ui-json`, and `CARET_SUITE_MODE=a2ui` alongside existing `--gui`, `--gui-frame-once`, and `--tui` modes.
- `cs_dashboard_session_views`: shared projection helper mapping `CsDashboard` agents into `SessionView` entries without duplicating state-axis logic.
