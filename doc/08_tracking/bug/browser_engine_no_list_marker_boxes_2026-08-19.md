# browser_engine: no `::marker` boxes generated for `<li>` (list bullets/numbers never rendered)

- **Date:** 2026-08-19
- **Status:** OPEN
- **Severity:** medium (every `<ul>`/`<ol>` renders without bullets or numbers; visual + geometry divergence from Chrome)
- **Module:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl` (box generation) — list-item display type produces no marker box

## Symptom

For plain `<ul>`/`<ol>` markup (fixture `tools/component_diff/fixtures/dom_zoo.html`),
Chrome emits a `::marker` pseudo-element box per `<li>`
(`#li1/::marker[0]`, `#li2/::marker[0]`, `#li3/::marker[0]`,
`#ol1/li[0]/::marker[0]`, `#ol1/li[1]/::marker[0]`). The Simple engine emits
none — 5 chrome-only node paths in
`tools/component_diff/out/dom_zoo/dom_zoo.state0.diff.txt` (Chrome for Testing
151.0.7922.34). The `<li>` principal boxes themselves are present and
indented, so the gap is specifically marker-box generation
(`display: list-item` marker semantics), not list layout as a whole.

## Repro

```
sh tools/component_diff/run_component_diff.shs --component dom_zoo
grep '::marker' tools/component_diff/out/dom_zoo/chrome/dom_zoo.state0.txt   # 5 lines
grep '::marker' tools/component_diff/out/dom_zoo/simple/dom_zoo.state0.txt  # 0 lines
```

## Pin

Divergence pinned shrink-only in
`test/03_system/browser_engine/chrome_component_set_spec.spl` (dom_zoo pin);
re-measure the pin when marker boxes land.
