---
id: js_engine_no_dom_bom_globals_2026-07-11
status: OPEN
severity: high
discovered: 2026-07-11
discovered_by: famous-page JS conformance probe (tools/pixel_compare/probe_js_char.spl)
related: src/lib/nogc_sync_mut/js/engine/runtime.spl
related: src/lib/nogc_sync_mut/js/engine/interpreter.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/script_runner.spl
---

# JS engine binds no DOM/BOM globals — famous-page DOM JS silently no-ops

**Status:** OPEN. Engine-core; filed by the browser-script-API agent (owns
`browser_engine/script/*`, does not own `js/engine/**`).

## Summary

When a page's `<script>` bodies are evaluated on `JsRuntime` (via
`run_page_scripts` → `JsRuntime.eval` → `_eval_browser_host_fast_path` +
`js_parse_program_subset` + interpreter), the browser global surface is
completely absent. `document`, `window`, `navigator`, and `localStorage` are
all `undefined`, so every DOM/BOM operation a real page performs returns
`undefined` **without throwing**. The `_eval_browser_host_fast_path` table is
100% Node builtins (`require('fs')`, `Buffer`, `process`, …); there is no DOM
wiring, and the interpreter's global environment defines none of the browser
globals.

Consequence: famous-page JS such as `document.getElementById('x').innerHTML = …`
never reaches the Simple DOM API (`browser_engine/script/dom_api.spl`); it is a
silent no-op. The DOM API layer is only reachable through the
`type="text/simple"` script lane, not the JS lane.

## Minimal repros (each is a full `JsRuntime.eval` source string)

```
typeof document        // => "undefined"   (expected "object")
typeof window          // => "undefined"   (expected "object")
typeof navigator       // => "undefined"   (expected "object")
typeof localStorage    // => "undefined"   (expected "object")
document.getElementById('foo')   // => undefined (no throw, no lookup)
window.location.href             // => undefined
navigator.userAgent              // => undefined
localStorage.setItem('k','v'); localStorage.getItem('k')  // => undefined
```

Reproduce: `bin/simple run tools/pixel_compare/probe_js_char.spl` and
`tools/pixel_compare/probe_js_lane.spl`.

## Expected

A browser `JsRuntime` should expose at minimum `document` (with
`getElementById`/`querySelector`/`querySelectorAll`/`createElement`),
`window`/`window.location`, `navigator.userAgent`, and `localStorage`, bridged
to the existing `browser_engine/script/*` API and the parsed `BeDomNode` tree
the `ScriptHost` already holds.

## Notes

Google's inline scripts in `google_live.html` (11 script bodies) all `eval`
without error precisely because they never depend on a populated DOM — they
return `undefined` and move on. No parser hang was observed on that corpus.
