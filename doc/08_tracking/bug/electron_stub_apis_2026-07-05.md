---
id: electron_stub_apis_2026-07-05
status: OPEN
severity: high
discovered: 2026-07-05
discovered_by: Code review of src/app/ui.electron/main.spl and src/app/ui.electron/bridge.js
related: src/app/ui.electron/main.spl
related: src/app/ui.electron/bridge.js
---

# Electron backend: stub APIs and missing multi-window (MDI) support

## Summary

Two critical gaps in the Electron backend block production use:

### 1. Stub IPC handlers in main.spl

Lines 135–149 of `src/app/ui.electron/main.spl` implement notification and file dialog as TODO(v4-dev-preview):

```simple
fn notify(title: text, message: text) -> bool:
    serial_println("IPC: notify called: " + title + " | " + message)
    return true  # stub — does NOT invoke Electron Notification API

fn open_file_dialog() -> text:
    serial_println("IPC: open_file_dialog called")
    return ""  # stub — does NOT invoke Electron dialog.showOpenDialog
```

Both return success without performing the requested action.

### 2. Single-window limitation in bridge.js

`src/app/ui.electron/bridge.js` line 943 and surrounding BrowserWindow management support only **a single window**, with no internal-window (MDI) surface routing.

The target architecture requires **multiple internal windows within a single BrowserWindow** (MDSOC+ ECS application model). Current bridge.js creates/manages only one window entry per app instance; subsequent window-creation calls cannot route to internal surfaces.

## Impact

- **notify()** and **open_file_dialog()** cannot perform their named actions; callers silently fail.
- **Multi-window apps** (MDI, tabbed workflows, sidebars as child windows) cannot render on Electron backend — a core MDSOC+ requirement.

## Scope

Electron backend (src/app/ui.electron/) is feature-incomplete relative to the self-hosted WM and Tauri backends. This is marked as v4-dev-preview, but blocks any production use of Electron on apps requiring these features.

## Related

- Target architecture: doc/04_architecture/ui/mdsoc_architecture_tobe.md (MDSOC+ section)
- Completed backends: Tauri (Android live, iOS sim-only), winit WM (macOS Metal + HTML web)
