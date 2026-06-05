# Low Dependency UI dynSMF Agent Plan TLDR

- Agent A: UI dependency boundaries.
- Agent B: dynSMF loader and session unload.
- Agent C: stdlib-like dynSMF manifests and opt-out policy.
- Agent D: HTML/CSS component loading.
- Agent E: specs, manuals, and verification evidence.
- Current first UI split target: keep `app.ui.tui` clean and split/gate
  `app.ui.render.widgets -> app.ui.render.html_widgets`.

```sdn
parallel_agents {
  A_ui_boundaries -> D_html_css_loading
  B_loader_unload -> C_manifests
  A_ui_boundaries + B_loader_unload + C_manifests + D_html_css_loading -> E_verify
}
```
