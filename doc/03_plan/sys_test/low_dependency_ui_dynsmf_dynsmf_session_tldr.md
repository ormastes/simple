# Low Dependency UI dynSMF Session TLDR

- Specs cover dynSMF manifests, default autoload, startup integration, arg/env
  opt-out, unload, stale handles, and reload.
- System coverage unloads and reloads all six selected default ids: `file_io`,
  `net_io`, `render2d`, `web_renderer`, `gui_renderer`, and `tui_renderer`.
- Startup integration lives in `src/app/startup/dynsmf_autoload.spl` and
  `src/app/main.spl --dynsmf-status`.
- Controls: `--no-dynsmf`, `--disable-dynsmf=<id>`,
  `SIMPLE_DYNSMF=0`, `SIMPLE_DYNSMF_DISABLE=<id>`.
- Generated manuals exist for unit, integration, and system dynSMF specs.

```sdn
dynsmf_session_test {
  manifest -> autoload
  app_startup -> status_evidence
  opt_out -> skipped
  all_defaults -> unload
  unload -> stale_handle
  stale_handle -> reload
  reload -> fresh_generation
}
```
