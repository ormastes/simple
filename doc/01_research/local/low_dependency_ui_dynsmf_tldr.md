# Low Dependency UI dynSMF Local Research TLDR

- Existing UI hot spots: `app.ui.web`, `app.ui.render.html_widgets`,
  `app.ui.web.html`, `app.ui.browser`, and `app.ui.tui`.
- Boundary concerns: TUI files mention web terms, VSCode imports HTML/CSS
  helpers directly, browser uses shared CSS types.
- Existing dynlib path already has SMF-aware close/unload in `dynlib.spl`,
  `dylib_async.spl`, `dylib_registry.spl`, and GUI dynlib probes.
- Existing `src/os/smf/smf_dynlib.spl` exposes SMF `dlopen`/`dlsym`/`dlclose`,
  but no stdlib-like dynSMF autoload manifest was found.
- Corrected import closure: base `app.ui.tui` currently has zero web,
  TUI-web, HTML, browser, CSS, or GUI implementation modules in closure.
- Main split target: `app.ui.render.widgets -> app.ui.render.html_widgets`.
- Main gap: no combined low-dependency UI plus stdlib-like dynSMF requirements
  or design.

```sdn
local_research {
  ui_contracts -> adapters
  adapters -> renderer_impls
  dynlib_facade -> smf_registry
}
```
