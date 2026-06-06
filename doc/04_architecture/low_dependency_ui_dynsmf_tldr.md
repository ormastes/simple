# Low Dependency UI dynSMF Architecture TLDR

- Selected: thin vertical slice.
- Base TUI stays behind common UI/TUI contracts.
- `app.ui.render.widgets` is now a TUI-only compatibility shim; HTML callers use
  `app.ui.render.html_widgets` directly.
- HTML/CSS implementations move behind explicit renderer capabilities.
- `app.ui.render.capability` declares HTML renderer, CSS provider, and TUI
  renderer boundaries without importing HTML/CSS implementations.
- Render adapters use `css_for_components([...])` to request only needed
  component styles.
- All six stdlib-like ids are default-autoload precompiled dynSMF manifest
  entries and route checked loads through `smf_dlopen_checked`; compatibility
  loads and symbol/close operations use `smf_dlopen`/`smf_dlsym`/`smf_dlclose`.
- Checked autoload validates generated `.smf` artifacts exist and start with
  `SMF\0` inside the lower checked SMF dynlib facade.
- `src/app/startup/dynsmf_autoload.spl` wires app startup to checked CLI/env
  dynSMF policy; app root exposes quiet-by-default `--dynsmf-status` evidence.
- Each manifest entry has a deterministic compile-to-SMF build plan under
  `build/dynsmf/`.
- Interpreter startup records general `compile_background` queue evidence for
  missing dynSMF artifacts before checked autoload fails closed; this is not a
  GUI-only path.
- Session evidence persists load, skip, symbol, stale, unload, and reload
  actions for interpreter-mode verification.
- Real package/build-output wiring can replace the facade-backed paths without
  changing the session contract.

```sdn
architecture {
  common_ui_contracts -> tui_base
  tui_widgets_shim -> html_free
  renderer_capability_registry -> html_css
  renderer_capability_registry -> implementation_free
  app_startup -> dynsmf_session
  app_startup -> background_compile_request
  dynsmf_session -> stdlib_like_dynsmf
}
```
