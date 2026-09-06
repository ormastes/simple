# Low Dependency UI dynSMF Dependency Gate TLDR

- Candidate specs will prove exact-prefix UI dependency closures.
- Current TUI base closure is clean; common render widgets still pull HTML
  widgets.
- Gate must report source module, forbidden dependency, and import path.
- No executable spec is created until final requirements are selected.

```sdn
dependency_gate {
  app.ui.tui -> no_web_html_css_gui
  app.ui.render -> widget_capability_gate
  adapters -> common.ui.web_render_api
}
```
