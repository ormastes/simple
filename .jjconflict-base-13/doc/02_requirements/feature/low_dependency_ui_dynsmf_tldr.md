# Low Dependency UI dynSMF Feature Requirements TLDR

- Selected: low-dependency UI slice plus all requested stdlib-like dynSMF
  manifest/autoload session behavior.
- Protect base `app.ui.tui` from GUI/web/TUI-web/browser/HTML/CSS implementation
  closure.
- Split or capability-gate `app.ui.render.widgets -> app.ui.render.html_widgets`.
- Add precompiled dynSMF manifest ids and compile-to-SMF build plans for all
  requested stdlib-like libraries.
- Implement session-owned default autoload, opt-out, unload, stale handle, and
  reload evidence for all six requested default dynSMF libraries.

```sdn
selected_slice {
  tui_dependency_gate
  html_css_capability
  all_default_dynsmf_session
  all_default_dynsmf_session -> unload_reload_evidence
}
```
