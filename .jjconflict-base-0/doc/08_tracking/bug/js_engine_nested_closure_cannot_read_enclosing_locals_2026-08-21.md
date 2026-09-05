# JS engine (nogc_sync_mut copy): a nested function cannot read its enclosing function's locals or parameters

- Date: 2026-08-21
- Status: RESOLVED 2026-08-21
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

## Resolution (2026-08-21)

Root cause: `src/lib/nogc_sync_mut/js/engine/interpreter_types.spl` — `class
Environment` carried no parent link, `EnvironmentStack.create_env(parent)`
DISCARDED its `parent` argument, and `get_var`/`set_var` searched only the
given frame plus frame 0 (globals). Every call site already passed the correct
lexical parent (`create_env(js_fn.closure_env)` in `interpreter_eval.spl:207,
470, 1391`, `interpreter_string_methods.spl:442`, `interpreter_async.spl:355`),
so the whole defect was the dropped link. That is exactly the reported shape:
own params fine, global writes fine, enclosing params/`var` locals undefined.

The engine fix landed in commit `bdc18a13495` ("fix(js): function-scope chain +
global String/Number/Boolean constructors in the JS engine") from a parallel
lane: `Environment.parent`, `create_env` storing it, and a chain-walking
`_resolve_env` used by both `get_var` and `set_var`. No further engine change
was needed here, so none was made.

What this change adds:
- `test/01_unit/lib/common/web/browser_session_js_closure_scope_spec.spl` (new,
  mirrored to `test/unit/lib/common/web/`): the six repro rows G/I/H/J/E/A above,
  plus two neighbours — an inner `var` must shadow without leaking outward, and
  an assignment in a nested callback must write THROUGH to the enclosing local
  (the `set_var` half of the same defect).
- `test/01_unit/lib/common/web/browser_session_async_spec.spl`: the `keep`
  script-global hoist in "keeps Response.bodyUsed read-only ..." is removed; the
  Response is now held by a genuinely nested `r.text().then(function (v) {...})`
  callback, the idiomatic Fetch shape.

Evidence (same spec file, same binary, only the engine file toggled):

    engine at bdc18a13495~1 (pre-fix):  8 total, 2 passed, 6 failed
        row I  expected undefined to equal 5
        row H  expected undefined:undefined to equal 5:5
        row J  expected undefined to equal 5
        row E  expected undefined:undefined to equal number:5
        row A  expected alpha:undefined:undefined to equal alpha:object:200
        write-through  expected 1 to equal 6
    engine at HEAD (fixed):             8 total, 8 passed, 0 failed

Neighbours, all on the fixed engine:
- `browser_session_async_spec.spl` (with the hoist removed): 25 total, 25 passed
- `browser_session_dom_generation_runtime_spec.spl`: 1 total, 1 passed

The "also observed" lexer note (an apostrophe inside a `//` comment breaking the
script) is NOT covered here and is not resolved by this change.
