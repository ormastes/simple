# Low Dependency UI dynSMF Loader Handoff TLDR

- Existing loader APIs register, open, resolve, and close SMF/dynlib handles.
- Implemented layer: session-owned dynSMF policy, autoload, skip-all/per-id
  disable, unload, stale-handle diagnostics, and reload with fresh state.
- Proposed controls: `--no-dynsmf`, `--disable-dynsmf=<ids>`,
  `SIMPLE_DYNSMF=0`, `SIMPLE_DYNSMF_DISABLE=<ids>`.
- Manifest ids: `file_io`, `net_io`, `render2d`, `web_renderer`,
  `gui_renderer`, `tui_renderer`.
- Build plans map each id to `bin/simple compile <source> -o build/dynsmf/<id>.smf`.
- Canonical build evidence:
  `scripts/check/check-low-dependency-dynsmf-build-plans.shs`.

```sdn
dynsmf_session {
  manifest -> policy -> autoload
  load -> symbol -> unload -> stale_handle
  reload -> fresh_generation
}
```
