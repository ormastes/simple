---
id: js_engine_missing_builtins_regex_promise_prototype_2026-07-11
status: OPEN
severity: medium
discovered: 2026-07-11
discovered_by: famous-page JS conformance probe (tools/pixel_compare/probe_js_char.spl)
related: src/lib/nogc_sync_mut/js/engine/interpreter.spl
related: src/lib/common/js/engine/runtime.spl
---

# JS engine: regex String.replace is a no-op, Promise undefined, prototype methods not introspectable

**Status:** OPEN. Engine-core; filed by the browser-script-API agent (does not
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
