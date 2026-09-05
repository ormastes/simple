# browser_engine: tree builder does not synthesize implicit `<tbody>` for `<table><tr>`

- **Date:** 2026-08-19
- **Status:** FIXED (2026-08-19 — verified: dom_zoo node-path sets identical to Chrome, comm -3 = 0; unit reproduce specs green in test/01_unit/browser_engine/html_tree_builder_spec.spl and chrome_component_set_spec dom_zoo pin re-measured 64/139 -> 70/145 with structural parity)
- **Severity:** medium (DOM structure diverges from every real browser; selectors/JS walking `table.tBodies`/`children` see a different tree)
- **Module:** `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl`

## Symptom

For `<table id="tb1"><tr><td>implicit tbody</td><td>x</td></tr></table>`
(fixture `tools/component_diff/fixtures/dom_zoo.html`), Chrome builds
`#tb1/tbody[0]/tr[0]/td[*]` — the HTML5 tree-construction algorithm inserts an
implicit `<tbody>` when a `<tr>` appears in the "in table" insertion mode.
The Simple engine builds `#tb1/tr[0]/td[*]` with NO tbody node.

Measured (Chrome for Testing 151.0.7922.34 vs `bin/simple run` extraction,
evidence `tools/component_diff/out/dom_zoo/dom_zoo.state0.diff.txt`):

- chrome-only paths: `#tb1/tbody[0]`, `#tb1/tbody[0]/tr[0]`, `#tb1/tbody[0]/tr[0]/td[0..1]` (+text)
- simple-only paths: `#tb1/tr[0]`, `#tb1/tr[0]/td[0..1]` (+text)

Explicit-`<tbody>` markup (fixture `table.html`) is unaffected — this is
purely the implicit-synthesis branch of the tree builder.

## Repro

```
sh tools/component_diff/run_component_diff.shs --component dom_zoo
comm -23 <(awk '{print $1}' tools/component_diff/out/dom_zoo/chrome/dom_zoo.state0.txt|sort -u) \
         <(awk '{print $1}' tools/component_diff/out/dom_zoo/simple/dom_zoo.state0.txt|sort -u)
```

## Pin

Divergence is pinned shrink-only in
`test/03_system/browser_engine/chrome_component_set_spec.spl` (dom_zoo pin).
Fixing this changes node paths, so the pin must be re-measured with the fix.
