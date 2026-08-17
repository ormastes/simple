---
id: js_engine_no_dom_bom_globals_2026-07-11
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
severity: high
discovered: 2026-07-11
discovered_by: famous-page JS conformance probe (tools/pixel_compare/probe_js_char.spl)
related: src/lib/nogc_sync_mut/js/engine/runtime.spl
related: src/lib/nogc_sync_mut/js/engine/interpreter.spl
related: src/lib/gc_async_mut/gpu/browser_engine/script/script_runner.spl
---

# JS engine binds no DOM/BOM globals — famous-page DOM JS silently no-ops

**Status:** OPEN — but re-characterized 2026-08-10. The engine is pure Simple
(`src/lib/nogc_sync_mut/js/engine/**`, NOT Rust seed), and it ALREADY has host
DOM/BOM identifier hooks: `window`/`self`/`document`/`location`/`navigator`/
`chrome`/`sessionStorage`/`localStorage` resolve at
`src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl:39-54` whenever the
corresponding `host_*_id >= 0`, and `document.title`/`cookie`/`body`/`location`
plus `body.innerHTML`/`textContent` member reads are handled in
`src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl` (host_document_id
branch). The actual gap is the WIRING: the `run_page_scripts` lane
(`src/lib/gc_async_mut/gpu/browser_engine/script/script_runner.spl`) creates
`js_runtime_with_default_logger` per script and never populates the host ids
from the parsed `BeDomNode` tree, so every `host_*_id` stays -1 and the
identifiers fall through to "undefined". Fix belongs in the script_runner /
ScriptHost bridge, not in engine core. (`typeof document` etc. now at least
route through the same identifier path after the 2026-08-10 typeof fix, so
wiring the host ids will make both evaluation and feature detection work.)

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

## Triage 2026-08-17 (lane m7c_lib_async) — UNVERIFIED on this host

Confirmed only that script_runner.spl mentions document/window in just 2 places, consistent with the doc's claim that no DOM/BOM globals are bound — but binding them is a feature build-out, not a defect patch, and no execution evidence was gathered. Not reproduced and not closed: this lane could neither exercise the path nor
find content-level evidence of a fix. Recording UNVERIFIED explicitly so it is
not mistaken for either a live confirmation or a close.
