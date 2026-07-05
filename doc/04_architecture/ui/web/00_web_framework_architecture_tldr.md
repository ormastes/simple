# Web Framework Architecture TLDR

The web framework owns routes, sessions, forms, and persistence. UI ownership
stays in Simple and connects to browser/native shells through `ui.web`.

```text
HTTP route
  -> app model/session/persistence
  -> Simple UI state
  -> UiAccessSnapshot + UIPatch
  -> ui.web WebSocket
  -> browser/Electron/SimpleWeb adapter   # SimpleWeb (web server ui) is default; Electron is non-default
```

Test and compatibility boundary:

```text
/api/test/*  -> UI test API, stable
/ui/ws       -> session snapshots, patches, input, host commands
```

Open next:

- `00_web_framework_architecture.md`
- `../ui_web_protocol.md`
- `web_stack_sample.md`
- `../00_ui_architecture.md`

