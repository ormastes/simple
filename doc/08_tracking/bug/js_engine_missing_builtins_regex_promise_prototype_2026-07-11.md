---
id: js_engine_missing_builtins_regex_promise_prototype_2026-07-11
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).
severity: medium
discovered: 2026-07-11
discovered_by: famous-page JS conformance probe (tools/pixel_compare/probe_js_char.spl)
related: src/lib/nogc_sync_mut/js/engine/interpreter.spl
related: src/lib/common/js/engine/runtime.spl
---

# JS engine: regex String.replace is a no-op, Promise undefined, prototype methods not introspectable

**Status 2026-08-10:** Items 2 and 3 FIXED; item 1 (regex replace) still OPEN.

The engine is pure Simple (`src/lib/nogc_sync_mut/js/engine/**`), not Rust seed.
Root cause of 2+3: `eval_unary`'s `typeof <Identifier>` branch used a
cache-only global lookup and never fell through to the normal identifier
resolution path (which already knew `Promise`, timers, and host globals) —
`src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl` (typeof branch, was
lines 378-397). And `eval_member` returned `Undefined` for builtin prototype
method names because those are dispatched by NAME at call sites only
(`interpreter_eval.spl` eval_call `_is_array_method`/`_is_string_method`
checks), never materialized as values —
`src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl` fallthrough.

Fix: typeof-Identifier now delegates to `eval_expression` (ReferenceError
suppression preserved: unknown identifiers still yield "undefined"), and
`eval_member` surfaces known array/string prototype methods as function
values. Regression spec (sabotage-verified RED→GREEN):
`test/01_unit/lib/js/typeof_builtin_introspection_spec.spl`.

Item 1 remains OPEN: regex literals reach `eval_call`'s string-method dispatch
but `replace` in `interpreter_string_methods.spl` only handles string search
arguments; a full regexp engine exists at `src/lib/common/js/builtins/regexp.spl`
but the nogc engine does not integrate it.

**Originally:** OPEN. Engine-core; filed by the browser-script-API agent (does not
own `js/engine/**` or `common/js/**`).

## Summary

Three builtin gaps in the subset JS interpreter, hit by everyday page JS:

1. **`String.prototype.replace` with a regex literal is a no-op.**
   ```
   'abc'.replace(/b/, 'X')   // => "abc"   (expected "aXc")
   ```

2. **`Promise` is undefined** — any `new Promise`, `Promise.resolve`,
   `.then/.catch`, or `async/await` page uses fail.
   ```
   typeof Promise            // => "undefined"   (expected "function")
   ```

3. **Prototype methods are not introspectable via property access** — `typeof`
   on a method property returns `"undefined"` even though the method is callable
   in call position.
   ```
   typeof [].forEach         // => "undefined"   (but [1,2,3].forEach(fn) runs)
   typeof ''.replace         // => "undefined"   (but ''.replace('a','b') works)
   ```
   Feature-detection code (`if (arr.forEach) …`, `if (el.addEventListener) …`)
   therefore takes the wrong branch.

Working for reference (so the gaps above are specific, not a dead interpreter):
`1 + 2` => 3; `[1,2,3].map(fn).join(',')` => "2,4,6"; `JSON.parse('[7,8]')[1]`
=> 8.

Reproduce: `bin/simple run tools/pixel_compare/probe_js_char.spl`.

## Expected

`String.replace(regex, repl)` performs regex substitution; `Promise` is defined;
`typeof obj.method === "function"` for present prototype methods.
