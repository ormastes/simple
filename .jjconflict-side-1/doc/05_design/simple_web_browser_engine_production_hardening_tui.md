<!-- codex-design -->
# Simple Web Browser Production TUI

## Primary surface

```text
[Back] [Forward] [Stop] [Reload] [Home] [Bookmark]
Address: https://example.test/page
Title: Example
Security: secure / verified
Status: ready

Example page
Name: Ada Lovelace
[Submit]
Animated status: frame 3
```

The TUI is the textual UI-access projection of the same BrowserSession state,
not a separate browser implementation.

## Actions

- `click`: chrome buttons, links, page buttons
- `set_value`: address and supported form controls
- `submit`: address and forms
- keyboard/pointer actions: canonical DOM event dispatch

## Evidence

Capture snapshots, action results, event history, navigation state, and visible
text under:

`build/test-artifacts/03_system/app/browser/feature/simple_web_browser_engine_production_hardening/`
