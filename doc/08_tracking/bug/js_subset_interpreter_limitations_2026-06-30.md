# Browser-session JS subset interpreter limitations

- **Date:** 2026-06-30
- **Component:** `src/lib/nogc_sync_mut/js/engine/` (interpreter_exec / interpreter_eval / parser)
- **Status:** Open
- **Severity:** Medium — forces workarounds in the ES-module transform
  (`src/lib/gc_async_mut/web/browser_session_modules.spl`).

## Summary

While fixing ES-module re-export support in `BrowserSession`, four independent
defects were found in the browser-session JS interpreter subset. Each was worked
around in the module transform layer rather than fixed in the engine (the engine
is large and shared; transform reshapes were lower risk). They should be fixed in
the engine so the transform can emit natural code.

All repros below use a **fresh `BrowserSession` + single `eval_script`** (chained
evals on one session give unreliable results — separate issue / harness caveat).
The reported value is the actual eval result.

## Defect 1 — member assignment inside an if/block body does not persist

```js
var o = {}; if (true) { o.a = 9; } o.a   // => undefined (expected 9)
var o = {}; if (true) o.a = 9; o.a       // => undefined (expected 9)
```

A plain `o.a = 9` at top level works, and member assignment inside a *function*
body works (`(function(){ g.a = 9; })(); g.a` => 9). Only assignments performed
inside an `if`/block statement body are lost. Looks like object-store mutations
made via `exec_if` / `Block` (`interpreter_exec.spl`) are not propagated back.

## Defect 2 — `class` + `new` + `this.member` broken

```js
class C { constructor(){ this.k = 7; } } var c = new C(); c.k   // => undefined
var B = class { constructor(){ this.k = 7; } }; new B().k        // => undefined
```

But a **function-expression constructor** works:

```js
var F = function(){ this.k = 7; }; var f = new F(); f.k          // => 7
```

So class declarations / class expressions instantiated via `new` do not bind
`this` members; only function-expression constructors do.

## Defect 3 — declared function/class names unusable as values

```js
function greet(n){ return 'hi ' + n; } var m = {}; m.default = greet; m.default('x') // => undefined
function g(n){ return n+1; } var x = g; x(4)                                          // => undefined
```

A function **expression** bound to a `var` is fine:

```js
var f = function(n){ return n+1; }; f(4)   // => 5
```

So a hoisted `function`/`class` declaration cannot be referenced by bare name as
a first-class value.

## Defect 4 — ternary mis-parses as assignment RHS

```js
var t = {}; t.x = true ? 5 : 9; t.x        // => true  (expected 5)
```

`t.x = cond ? a : b` assigns the *condition* value rather than the selected
branch — the `? a : b` tail is dropped. (`t.x = t.b || 5` logical-or works
correctly, => 5.)

## Workarounds applied (commit e0e4ddfa9aab)

The module transform now emits only forms the subset supports:
- function/class exports → `var X = function(...){...}` expressions (Defects 2, 3).
- `export * from` precedence guard → `X = X || dep.X` instead of
  `if (X == undefined) X = dep.X` (Defect 1).
- Ternary avoided entirely (Defect 4).

### Known semantic deviation from the workaround

`export *` precedence via `X = X || dep.X` differs from strict ES semantics: a
**falsy** local export (`0`, `""`, `false`, `null`) of the same name as a star
re-export would be wrongly overwritten by the dependency's value. The five system
tests only exercise truthy export values, so they pass; a correct fix needs
Defect 1 resolved so an `undefined`-guard can be used.
