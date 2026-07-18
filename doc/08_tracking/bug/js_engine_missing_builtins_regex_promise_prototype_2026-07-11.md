---
id: js_engine_missing_builtins_regex_promise_prototype_2026-07-11
status: PARTIAL
severity: medium
discovered: 2026-07-11
partial_fix: 2026-07-18
discovered_by: famous-page JS conformance probe (tools/pixel_compare/probe_js_char.spl)
related: src/lib/nogc_sync_mut/js/engine/interpreter.spl
related: src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl
related: src/lib/nogc_sync_mut/js/engine/interpreter_eval_member.spl
related: src/lib/nogc_sync_mut/js/engine/interpreter_string_methods.spl
related: src/lib/nogc_sync_mut/js/engine/parser.spl
related: src/lib/js/types/ast_types.spl
related: src/lib/common/js/builtins/regexp.spl
---

# JS engine: regex String.replace is a no-op, Promise undefined, prototype methods not introspectable

**Status:** PARTIAL (2026-07-18, lane N5). Do not close — real gaps remain.
The three CONCRETE repros literally shown in this doc's "Summary" section now
pass: regex-literal `String.prototype.replace`, `typeof Promise`, and `typeof`
on array/string prototype methods. But this doc's own item 2 also claims
"`new Promise`, ... `.then/.catch` ... fail" more broadly — `new Promise(executor)`
construction is still broken (confirmed, see below) and is deliberately
deferred, not fixed. Root causes and fixes below; see "Remaining / deferred"
for everything intentionally left out — keep this doc open until that list is
cleared or re-triaged into its own tracked item.

Note: `related:` above corrects the original filing — the actual bound
`std.js.types.ast_types` is the untiered `src/lib/js/types/ast_types.spl` (not
`src/lib/common/js/types/ast_types.spl`, which — along with
`src/lib/nogc_sync_mut/js/types/ast_types.spl` — is an orphaned duplicate that
nothing imports). `src/lib/common/js/engine/runtime.spl` is a separate,
unrelated JS engine copy not used by `run_page_scripts`/`JsRuntime`; the
runtime actually used is `src/lib/nogc_sync_mut/js/engine/runtime.spl`.

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

## Root causes and fixes

1. **Regex literal — no AST support at all, plus an orphaned regex engine.**
   The subset expression parser (`_js_parser_expression` in
   `nogc_sync_mut/js/engine/parser.spl`) had zero notion of `/pattern/flags` —
   `/` was always scanned as the multiplicative division operator, so
   `.replace(/b/, 'X')` parsed as `(/b) / 'X'`-ish garbage, evaluated `b` as an
   undefined identifier, and `String.prototype.replace` (which always did
   `js_to_string()` on its first arg) silently no-op'd. Separately, a
   fully-working regex engine (`RegExpObj`, `string_replace`, `string_match`,
   `regexp_test/exec`, `.`/`\d`/`\w`/`\s`/char-classes/`*+?`/anchors/`|`) already
   existed at `src/lib/common/js/builtins/regexp.spl` — but nothing imported it.
   Fix: added `JsExpression.RegexLiteral(pattern, flags)` to the real bound AST
   (`src/lib/js/types/ast_types.spl`); added `_js_parser_try_regex_literal` to
   the parser, recognizing a **bare** regex literal that spans an entire
   expression (a call argument, assignment RHS, or standalone statement — e.g.
   `str.replace(/b/, 'X')`, `var re = /a+b/i;`); `eval_expression` materializes
   it via a new `_create_regex_value` as a plain object
   (`source`/`flags`/`global`/`ignoreCase`/`multiline`/`lastIndex` +
   `__simple_is_regexp` marker) rather than a new `JsValue` variant (avoids
   rippling through every exhaustive `match` on the ~9K-line
   `interpreter_native.spl`); `String.prototype.replace` now detects that
   marker and calls the existing (now finally wired-in) `string_replace`.

2. **`typeof Promise` (and other pseudo-globals) — duplicated, drifted
   special-case list.** `eval_expression`'s `Identifier` branch special-cases
   `window`/`document`/`Promise`/`Buffer`/`process`/`require`/`setTimeout`/etc.
   as pseudo-globals, but `eval_unary`'s `typeof` handling reimplemented
   identifier resolution separately and only knew about `setImmediate`/
   `clearImmediate`, defaulting everything else to `"undefined"` even though
   the same identifier resolved fine outside of `typeof`. Fix: `typeof` on an
   identifier now falls through to `eval_expression` (single source of truth)
   instead of hard-coding `"undefined"`, fixing `typeof window`/`document`/
   `Buffer`/`process`/`require`/`setTimeout`/`clearTimeout` too as a side
   effect. `Promise` itself needed one more line: the interpreter represents
   it internally as a plain object (constructor + prototype methods as own
   properties, not a `JsValue.Function`), so a small explicit override reports
   `typeof Promise === "function"` to match real JS (`Promise.resolve`/
   `.reject`/`.then`/`.catch`/`.finally` were already implemented and working
   pre-fix — verified via `Promise.resolve(5)` returning a real object at HEAD).

3. **Prototype methods not introspectable.** Array/string prototype methods
   (`forEach`, `replace`, ...) are dispatched natively at the **call site**
   (`eval_call`'s `Member`-callee handling matches method names directly) and
   are never stored as real object/string properties, so a bare property
   access (`eval_member`, used for `typeof x.method` and `if (x.method)`
   feature-detection) found nothing and returned `Undefined`. Fix: `eval_member`
   now falls back to synthesizing a `JsValue.Function` marker when the
   property name is a known array method (`_is_array_method`) or string method
   (`_is_string_method`) and no real property/prototype value was found —
   sufficient for `typeof`/truthiness checks; actual calls are unaffected
   (they never went through this path).

## Verification

Reproducing test: `test/01_unit/lib/common/js_runtime_builtins_regex_promise_prototype_spec.spl`
(7 examples — regex replace incl. first-match-only and character-class cases,
`typeof Promise`, `typeof` on array/string prototype methods, plus the doc's
original working reference scripts). Confirmed red at baseline (6/7 failing,
matching this doc exactly) and green after the fix (7/7). Re-ran
`tools/pixel_compare/probe_js_char.spl` (the doc's original repro): indices
5/6/7 (`typeof [].forEach` / `typeof ''.replace` / `typeof Promise`) now print
`function` instead of `undefined`.

Regression spot-check (not a full sweep):
`test/01_unit/lib/common/js_runtime_host_property_spec.spl`,
`js_runtime_node_fast_path_spec.spl`, `js_async_fetch_spec.spl` all ran to
completion and passed. `browser_script_execute_spec.spl` has one pre-existing,
unrelated failure ("stack overflow: recursion depth 1000 exceeded limit 1000
in function 'trim'" in pixel rendering) confirmed present identically on
unmodified HEAD — not a regression from this change.
`simple_script_spec.spl` timed out under heavy concurrent load from other
parallel lanes (90s) and was **not run to completion** — treat it as
unverified, not passing.

## Remaining / deferred (out of scope for this fix)

- `new Promise(executor)` construction still returns `undefined`: `eval_new`
  only handles `JsValue.Function` callees, and `Promise` evaluates to a
  `JsValue.Object`. `Promise.resolve`/`reject`/`.then`/`.catch`/`.finally`
  already work. Implementing executor-based construction (synchronously
  invoking the executor with bound `resolve`/`reject` callbacks tied to a
  specific pending-promise id) is a distinct, larger unit of work against the
  existing settle/handler infrastructure in `interpreter_native.spl`.
- Regex literals are only recognized when they form a **whole** expression
  (call argument / assignment RHS / statement). Chaining directly off a
  literal (`/re/.test(x)`) is not parsed as a regex — the text-slicing parser
  has no general notion of a regex span in its top-level operator/comma
  scanners, only in `_js_parser_expression`'s new whole-literal check and the
  pre-existing balance-checker. Use `new RegExp(...)`-free code that assigns
  the literal to a variable first, or pass it directly as a call argument.
- `String.prototype.match`/`.search`/`.split`/`.replaceAll` and
  `RegExp.prototype.test`/`.exec` do not yet detect the regex marker object
  (only `.replace` was wired, matching this doc's concrete repro). The
  underlying `regexp.spl` functions (`string_match`, `regexp_test`,
  `regexp_exec`, `string_split_regex`) already exist and can be wired the same
  way `.replace` was.
- `new RegExp(pattern, flags)` (constructing a regex from strings, not a
  literal) is not implemented.
- This fix only touches the `nogc_sync_mut` JS engine copy (the one
  `run_page_scripts`/`JsRuntime` actually exercises). The sibling engine
  copies under `src/lib/gc_async_mut/js/engine/` and
  `src/lib/nogc_async_mut/js/engine/` are separate forks with the same latent
  gaps (no regex-literal AST support, same `typeof`/prototype-introspection
  shape) and were not touched — if those tiers are ever exercised directly,
  expect the same three symptoms there.
