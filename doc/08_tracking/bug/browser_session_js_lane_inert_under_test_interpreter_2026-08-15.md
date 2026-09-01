# BrowserSession JS script lane inert under the test interpreter (2026-08-15)

**Status:** open
**Area:** `src/lib/gc_async_mut/web/browser_session*.spl`, `src/lib/*/js/engine/**`
**Specs blocked:**
- `test/01_unit/browser_engine/browser_script_execution_spec.spl` — 0/4
- `test/01_unit/browser_engine/browser_animation_clock_spec.spl` — 1/2
  (only the requestAnimationFrame example; the CSS keyframes example passes,
  it uses no JS)

## Symptom

Under `bin/simple test` (tree-walk interpreter), every page script fails and
`session.render_html_document()` returns the `about:blank` placeholder
document, so all DOM-mutation assertions fail:

```
[WARN] [browser-session] ReferenceError: for is not defined
[WARN] [browser-session] ReferenceError: __simple_i is not defined
[WARN] [browser-session] Invalid assignment target
[WARN] [browser-session] TypeError: undefined is not a function
[WARN] [browser-session] ReferenceError: ticks is not defined
assert_contains failed: '<!DOCTYPE html>...<title>about:blank</title>...' does not contain 'AfterScript'
```

The first four WARNs are raised by the session's own internal DOM-install
bootstrap script (`browser_session.spl:1811`, the `__simple_dom_install`
blob), not by page JS: `for (var __simple_i = ...)` is being parsed as an
IDENTIFIER expression (`for is not defined`), i.e. the JS statement parser is
not engaged at all in this closure. Even a top-level `var ticks = 0;`
declaration does not register (`ticks is not defined` on later
`eval_script("ticks")`). The wasm example additionally dies with
`semantic: array index out of bounds: index is 0 but length is 0`.

## Evidence that the engine itself is not simply missing `for`

- `src/lib/common/js/engine/lexer.spl:90` and `js_token.spl:373` both map
  `for` to a keyword token; `src/lib/nogc_async_mut/js/engine/
  interpreter_exec.spl:43` executes `JsStatement.For`.
- The failures occur inside the big co-compiled closure the spec pulls in
  (`std.gc_async_mut.web.browser_session*` + browser_engine + js engines).
  That closure emits many `compiler_cross_module_private_symbol_collision`
  warnings; four parallel JS engine trees (`common/js`, `nogc_sync_mut/js`,
  `nogc_async_mut/js`, `gc_async_mut/js` facade) share function names, so a
  `$dupN` ambiguous-fallback dispatch to the wrong family's parser/executor
  is the prime suspect (same mechanism as the `parse_int` collision fixed the
  same day in `net/h1_client.spl`, see the triage that accompanied this
  record).

## Repro

```
bin/simple test test/01_unit/browser_engine/browser_script_execution_spec.spl --no-session-daemon
bin/simple test test/01_unit/browser_engine/browser_animation_clock_spec.spl --no-session-daemon
```

## Unblock condition

`BrowserSession.open_html` + `render_html_document` must execute the inline
`<script>` and serialize the mutated DOM under the test interpreter. First
step: reproduce the internal bootstrap failure in isolation and determine
which JS parser implementation actually receives the source in this closure
(instrument the WARN site), then de-duplicate the colliding js-engine symbol
sets so dispatch is deterministic.
