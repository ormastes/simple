# Low Dependency UI dynSMF Detail Design TLDR

- Selected: thin vertical slice.
- Implement exact-prefix dependency policy and evidence over `use` and
  `export use`.
- Verify real `app.ui.tui.backend` and TUI-only `app.ui.render.widgets`
  closures.
- Gate HTML/CSS through renderer capabilities.
- Keep capability metadata in `app.ui.render.capability` implementation-free;
  HTML/CSS modules declare lazy capabilities.
- `css_for_components([...])` deduplicates requested component styles and the
  migrated adapters use it instead of direct CSS function concatenation.
- Implement `DynSmfManifestEntry`, `DynSmfSession`, and evidence rows for the
  six stdlib-like default dynSMF libraries through the existing SMF dynlib
  facade.
- Add deterministic compile-to-SMF build plans for the six `build/dynsmf/*.smf`
  outputs.
- Validate checked dynSMF artifacts with `DynSmfArtifactStatus` and
  `smf_dlopen_checked`; missing, short, or invalid magic fails before a handle
  is accepted.
- Wire app startup to checked dynSMF autoload from CLI/env policy while keeping
  plain app-root startup quiet and exposing `--dynsmf-status` evidence.
- Prove persisted symbol evidence, unload, stale lookup, and reload.

```sdn
detail_design {
  dependency_policy -> closure_gate
  renderer_capability -> html_css_gate
  renderer_capability -> implementation_free_registry
  startup_policy -> dynsmf_session
  dynsmf_session -> stdlib_like_dynsmf
}
```
