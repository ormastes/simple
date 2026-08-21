# JS engine (nogc_sync_mut copy): a nested function cannot read its enclosing function's locals or parameters

- Date: 2026-08-21
- Status: OPEN
- Engine copy: `src/lib/nogc_sync_mut/js/engine/` (the copy `BrowserSession` resolves to)
- Found while: adding a `bodyUsed` neighbour to `test/01_unit/lib/common/web/browser_session_async_spec.spl`

## Reproduce (each run through `BrowserSession.open_html` + `eval_script("out")`)

| # | script | real JS | this engine |
|---|---|---|---|
| G | `function f(x) { out = '' + x; } f(5);` | `5` | `5` |
| I | `function f(x) { [1].forEach(function(v) { out = '' + x; }); } f(5);` | `5` | `undefined` |
| H | `function f(x) { var y = x; [1].forEach(function(v) { out = '' + y + ':' + x; }); } f(5);` | `5:5` | `undefined:undefined` |
| J | `var g = function(x) { [1].forEach(function(v) { out = '' + x; }); }; g(5);` | `5` | `undefined` |
| E | `function f(x) { return Promise.resolve(1).then(function(v) { out = '' + (typeof x) + ':' + x; }); } f(5);` | `number:5` | `undefined:undefined` |
| A | `fetch('/t').then(function(r) { return r.text().then(function(v) { out = v + ':' + (typeof r) + ':' + r.status; }); });` | `alpha:object:200` | `alpha:undefined:undefined` |

Direct parameter access works (G). Any function nested one level deeper sees
the enclosing function's parameters AND `var` locals as `undefined` (I, H, J,
E, A), whether invoked synchronously (`forEach`) or from a promise job. Writes
to script GLOBALS from the nested function work, and reading the nested
function's OWN parameter works — which is why every existing browser_session
spec passes: they only read their own params and write globals.

Every `fetch(...).then(function(r) { ... r.text().then(function(v) { ...r... }) })`
shape — the idiomatic way to keep a `Response` in scope across a body read —
is silently wrong on this engine.

## Workaround used in the spec

Hoist the captured value to a script global (`var keep; ... keep = r;`) and
read `keep` in the nested callback. Marked in the spec with a comment pointing
here; remove the workaround when this is fixed.

## Also observed (not separately filed)

A `//` line comment containing an apostrophe (`function's`) inside the inline
`<script>` made the whole script fail to parse (`out` evaluated to
`undefined`). Moving the comment out of the JS fixed it. Likely the lexer
treats `'` inside `//` comments as a string opener; verify when fixing.

## No seed (Rust) change is required.
