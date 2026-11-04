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

**Re-verified LIVE 2026-08-17 by content.** `grep -rn "Regex\|RegExp\|regexp"
src/lib/nogc_sync_mut/js/` returns exactly ONE hit — a lexer comment at
`engine/parser.spl:1048` about skipping over a regex literal. There is no
`RegExp` value, no `JsValue` variant for one, and no integration of
`src/lib/common/js/builtins/regexp.spl`. `interpreter_string_methods.spl:271-300`
implements `replace` as a literal substring scan over `js_to_string(search_val)`
only, so a regex argument degrades to a text comparison and the call is a
silent no-op. Not fixed here: this is not a small change — it needs a new
`JsValue` regex variant, literal evaluation, and a regexp engine binding, which
is a feature-sized piece of work, not a patch.

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

## 2026-08-09 re-verification (worktree agent)

Re-ran `tools/pixel_compare/probe_js_char.spl` fresh in an isolated worktree
(seed binary, no self-hosted `bin/simple` deployed there). Non-DOM builtins
still behave as the doc's "working for reference" list states (`[8] 8.0`,
`[9] 2,4,6` for arithmetic/array-map-join), and the probe still reports the
DOM-blocked slots as `undefined` (see sibling doc
`js_engine_no_dom_bom_globals_2026-07-11.md` for that overlap). Did not
isolate a standalone regex/Promise/prototype-introspection-only repro in this
pass; the gaps this doc names (regex-`replace` no-op, `Promise` undefined,
`typeof obj.method`) are genuine subset-interpreter feature gaps in
`src/lib/nogc_sync_mut/js/engine/interpreter.spl` /
`src/lib/common/js/engine/runtime.spl` — implementing regex substitution, a
`Promise` object, and prototype-property reflection is new engine-core
functionality, not a scoped bugfix. **Confirmed ARCHITECTURAL-OPEN**, left as
filed; no root-cause fix applied in this session.

## Expected

`String.replace(regex, repl)` performs regex substitution; `Promise` is defined;
`typeof obj.method === "function"` for present prototype methods.

## Note 2026-11-04 — item 1 (regex replace) implemented; store-backed verification blocked on Windows seed

Implemented on `work/feat-js-regex-replace-20261104` (PR against `release/1.0.0`):

- `engine/parser.spl`: `_js_parser_regex_literal_end` applies the standard
  JS rule (a `/` starts a regex literal when the previous significant token
  cannot end an expression, via the existing `_js_regex_context`) and every
  quote-aware scanner (`find_top_level*`, ternary, assignment, split,
  matching paren/bracket/brace, `primary_end`) skips the literal. A literal
  `/src/flags` desugars to `new RegExp("src", "flags")` — no AST change.
- `RegExp` is a lazily registered native constructor
  (`NATIVE_REGEXP_CONSTRUCTOR`, same pattern as `String`/`Number`); a RegExp
  value is a plain object tagged `__simple_regexp` with `source`, `flags`,
  `global`, `ignoreCase`, `multiline`, `lastIndex` and native `test`/`exec`.
- `String.prototype.replace` routes a tagged search value through
  `src/lib/common/js/builtins/regexp.spl` (`g` honoured, function replacers
  called with `(match, offset, string)`, `$&`/`$$` expanded — also for plain
  string searches); `String.prototype.match` added (`null` on no match).
- Residual: `$1`/capture groups are not available (the regexp engine records
  no groups); `/` after `)` is still read as division; regex literals
  containing `;` or `{` still confuse the statement splitter.

Spec: `test/01_unit/lib/nogc_sync_mut/js/engine/regex_literal_replace_spec.spl`
— 13/13 on the Windows Rust seed once the object-store defect below was fixed.

Root cause of the initial 3/13: every `JsInterpreter.set_object_property` ->
`get_object_property` round-trip returned `undefined` on this host because the
seed *interpreter* drops a nested `self.object_store.<array>.push(x)` /
`[i] = x` made from another class's `me` method (the array is read as a
copy; the JIT keeps it, but the engine runs interpreted since
`JsInterpreter._run_promise_task` fails HIR lowering). Fixed in the same
branch by routing those writes through `ObjectStore` `me` methods
(`alloc_object`, new `update_slot` / `append_slot`) in the nogc_sync_mut,
nogc_async_mut and gc_async_mut `interpreter_object.spl`; `EnvironmentStack.new`
added to nogc_sync_mut. That took the pre-existing JS-engine specs from
1/6 green to 4/6 (remaining: nogc_sync_mut `js_vm_reclamation` is an
intentional RED placeholder; common `js_vm_reclamation` 2/4 reads the common
family's `env_parent_ids` field against the nogc_sync_mut engine).

## Note 2026-11-05 — capture groups, `new Promise(executor)`, `new C(args).m()` parsing

On `work/feat-js-builtins-promise-proto-20261105` (PR against `release/1.0.0`):

- **Item 1 residual (`$1` / capture groups) — DONE.** The 2026-11-04 note's
  "the regexp engine records no groups" understated it: `_match_atom` treated
  `(` as a literal character, so `(…)` never matched, and `_try_match` on
  reaching a top-level `|` after a successful left branch re-ran the right
  branch instead of succeeding, so plain alternation was a no-op too
  (`'xay'.replace(/a|b/, 'Z')` returned `xay`). `src/lib/common/js/builtins/regexp.spl`
  is now a compiled backtracking matcher (node arena + explicit continuation
  stack): groups, `(?:…)`, nested/quantified groups, `|`, `{n}`/`{n,}`/`{n,m}`,
  lazy quantifiers, `\b`/`\B`, class escapes inside `[...]`, `m` flag. `MatchResult`
  carries `groups: [text]` + `group_set: [bool]` (unmatched group = JS `undefined`).
  Engine side: `$1`..`$99` in string replacers, `(match, p1..pn, offset, string)` for
  function replacers, groups at `[1..n]` on non-global `match` and `exec`.
- **Item 2 (`new Promise`) — was NOT fixed by the 2026-08-10 change** despite the
  "FIXED" line above: `Promise` is a plain host object, so `new Promise(fn)` fell
  through `eval_new` to `undefined`. Now `eval_new` routes the host Promise object
  to `_construct_promise` (`interpreter_async.spl`): executor runs synchronously
  with native resolve/reject functions (ids `NATIVE_PROMISE_EXECUTOR_*`, target
  promise id carried in the native's name), settle-once, thenable adoption, and
  `then`/`catch` reactions stay microtask-deferred. A separate parser defect hid
  this: the subset parser read `new C(args).then(...)` as `new (C(args).then(...))`
  (`_js_parser_expression`, `new ` branch) — fixed by re-parsing as
  `(new C(args)).then(...)`.
- **Still open from this record's own list:** `async/await` — `AsyncFnDecl` /
  `Await` are not handled anywhere in `src/lib/nogc_sync_mut/js/engine/` (the
  subset parser emits neither), and the tree-walking interpreter has no
  suspension point to resume after an `await`; this is a feature, not a patch.
  Also not covered: `Promise.all`/`race` (not in this record), `throw`/`try` are
  not parsed by the subset parser, so a `throw` inside an executor or a `.then`
  handler cannot reject a promise (the full parser's `ThrowStmt` is a different
  `ast_types` enum from the one this engine matches, so it is no route either),
  `RegExp.prototype.exec` ignores `lastIndex` on `g` regexes, `C.prototype.m = fn`
  methods are not found on `new C()` instances, and a *quantified group* (`(ab)+`)
  recurses once per repetition, so several hundred repetitions hit the seed
  interpreter's 1000-frame limit (single-character quantifiers such as `\s+` /
  `\w+` are iterative and verified on 800-char inputs). `_run_promise_task` HIR-lowering
  claim from the 2026-11-04 note was not re-verified here (no diagnostic surfaced
  under `SIMPLE_JIT_TRACE=1`).

Specs (Windows Rust seed `D:/dev/wt/seed/simple.exe`):
`test/01_unit/lib/nogc_sync_mut/js/engine/regex_literal_replace_spec.spl`
13/17 -> 17/17 (4 new cases RED on the unpatched lib);
`test/01_unit/lib/nogc_sync_mut/js/engine/promise_constructor_spec.spl`
1/6 -> 6/6.
