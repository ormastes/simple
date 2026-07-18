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

**Status:** PARTIAL (2026-07-18, lanes N5 + B2). Do not close — real gaps
remain. The three CONCRETE repros literally shown in this doc's "Summary"
section now pass: regex-literal `String.prototype.replace`, `typeof Promise`,
and `typeof` on array/string prototype methods (lane N5). Lane B2 then closed
every regex gap N5 had deferred: chained regex-literal calls (`/re/.test(x)`,
`/re/.exec(x)`), `String.prototype.match`/`.search`/`.split`/`.replaceAll`
consuming a regex-literal argument, `RegExp.prototype.test`/`.exec`, and
`new RegExp(pattern, flags)` — see "Remaining / deferred" for what's left.
But this doc's own item 2 also claims "`new Promise`, ... `.then/.catch` ...
fail" more broadly — `new Promise(executor)` construction is still broken
(confirmed, see below) and is deliberately deferred, not fixed. Root causes
and fixes below; see "Remaining / deferred" for everything intentionally left
out — keep this doc open until that list is cleared or re-triaged into its
own tracked item.

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
   **Update:** `Promise.resolve/reject/.then/.catch/.finally` and `typeof
   Promise` were fixed in an earlier pass (see git history around commit
   `bac65baa7b1`), but `new Promise((resolve, reject) => {...})` construction
   still returned `undefined` — `eval_new` only matched a `JsValue.Function`
   callee, while the `Promise` identifier resolves to a plain host object.
   Fixed: `new Promise(executor)` now creates a real pending promise, runs the
   executor synchronously, and settles it via bound `resolve`/`reject`
   callbacks (see `src/lib/nogc_sync_mut/js/engine/interpreter_eval.spl`
   `eval_new` and `interpreter_async.spl` `_eval_new_promise`). Regression
   spec: `test/01_unit/lib/common/js_runtime_new_promise_executor_spec.spl`.

   **Deferred, separate gap found while fixing the above:** the subset parser
   mis-parses a postfix chain immediately after `new Ctor(...)`, e.g.
   `new Promise(executor).then(cb)` is parsed as if `.then(cb)` were an
   argument to the `new` expression itself (`_js_parser_expression`'s `new `
   handling in `parser.spl` greedily consumes the whole postfix chain via
   `_js_parser_postfix` and reattributes the trailing call). Workaround:
   assign to a variable first — `var p = new Promise(executor); p.then(cb);`.
   Not fixed here; scope was the executor/construction bug only.

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

## Lane B2 (2026-07-18) — closed the deferred regex gaps

All four regex items N5 left in "Remaining / deferred" below are now fixed,
wired through the existing `src/lib/common/js/builtins/regexp.spl` engine:

- **Chained regex-literal calls.** `_js_parser_expression` only recognized a
  regex literal spanning an entire expression, so `/re/.test(x)` fell through
  to the multiplicative `/` scan and misparsed as division. Added
  `_js_parser_try_regex_literal_chain` (parser.spl): when a regex literal is
  followed by a member/call/computed-member chain that consumes the *rest* of
  the expression, it's parsed as `RegexLiteral` + postfix chain instead
  (factored the postfix loop into `_js_parser_postfix_continue` so it can
  resume after the literal). Conservative by design: if something trails the
  chain that it can't consume (e.g. `/re/.test(x) && y`), it returns nil and
  defers to the pre-existing scanners — verified this composes correctly
  in practice because the higher-precedence `&&`/`||`/etc. scans run *before*
  the multiplicative `/` scan, splitting the expression first.
- **`String.prototype.match`/`.search`/`.split`/`.replaceAll` +
  `RegExp.prototype.test`/`.exec`.** All now detect the `__simple_is_regexp`
  marker the same way `.replace` already did, calling `string_match`,
  `regexp_exec`, `string_split_regex`, and `RegExpObj.create` respectively.
  `.replaceAll` on a regex forces the `g` flag rather than throwing (this
  subset interpreter doesn't have TypeError-on-missing-flag machinery).
  `RegExp.prototype.test`/`.exec` (wired in `eval_call`, interpreter_eval.spl)
  maintain `lastIndex` statefully for global regexes, matching real JS
  iteration semantics.
- **`new RegExp(pattern, flags)`.** `eval_new` special-cases
  `ident_name(callee) == "RegExp"` and builds the same marker object as a
  regex literal via the existing `_create_regex_value`; accepts either a
  string pattern or an existing regex value (copy-with-new-flags) as the
  first argument.

Reproducing tests added to
`test/01_unit/lib/common/js_runtime_builtins_regex_promise_prototype_spec.spl`
(new `describe` block, 8 `it`s / 17 assertions). Confirmed red at baseline
(0/17, via temporary revert of the 3 implementation files) and green after
(17/17). Regression spot-check: all of N5's original 7 `it`s plus plain
(non-regex) `.split`/`.replace`/`.replaceAll` and division expressions
(`10 / 2`, `(4 / 2) / 2`) still pass (20/20).

**New pre-existing gap noted (not fixed, out of scope):** `new Foo().method()`
— calling a method chained directly onto a `new` expression without an
intermediate variable — is mis-parsed for **any** constructor, not just
`RegExp`. `_js_parser_expression`'s `"new "` handling runs
`_js_parser_postfix` over the *entire* remainder and takes whichever `Call`
node comes out outermost as the constructor's args, so `new RegExp(...).test(x)`
parses as `NewExpr(callee: Member(Call(Identifier(RegExp), [...]), "test"),
args: [x])` instead of `Call(Member(NewExpr(RegExp, [...]), "test"), [x])`.
Confirmed with an unrelated user-defined constructor
(`new F().m()` also throws `ReferenceError: F is not defined`) — a general
parser-precedence bug predating this lane, unrelated to regex. Workaround:
assign the `new` expression to a variable first (`var re = new RegExp(...);
re.test(x)`), which is what the added tests use.

## Remaining / deferred (out of scope for this fix)

- `new Promise(executor)` construction still returns `undefined`: `eval_new`
  only handles `JsValue.Function` callees, and `Promise` evaluates to a
  `JsValue.Object`. `Promise.resolve`/`reject`/`.then`/`.catch`/`.finally`
  already work. Implementing executor-based construction (synchronously
  invoking the executor with bound `resolve`/`reject` callbacks tied to a
  specific pending-promise id) is a distinct, larger unit of work against the
  existing settle/handler infrastructure in `interpreter_native.spl`.
- `new Foo().method()` direct-chain parsing (see "Lane B2" above) — a general,
  pre-existing parser-precedence gap affecting any constructor, not specific
  to regex.
- This fix only touches the `nogc_sync_mut` JS engine copy (the one
  `run_page_scripts`/`JsRuntime` actually exercises). The sibling engine
  copies under `src/lib/gc_async_mut/js/engine/` and
  `src/lib/nogc_async_mut/js/engine/` are separate forks with the same latent
  gaps (no regex-literal AST support, same `typeof`/prototype-introspection
  shape) and were not touched — if those tiers are ever exercised directly,
  expect the same symptoms there.
