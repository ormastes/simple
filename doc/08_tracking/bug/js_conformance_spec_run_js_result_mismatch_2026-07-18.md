---
id: js_conformance_spec_run_js_result_mismatch_2026-07-18
status: OPEN
severity: high
discovered: 2026-07-18
discovered_by: lane C8 (new-expression postfix-precedence fix), while trying to
  run the js_runtime spec family as a regression check
related: test/03_system/feature/js/es5_conformance_spec.spl
related: test/03_system/feature/js/es2015_conformance_spec.spl
related: test/03_system/feature/js/interpreter_vars_spec.spl
related: src/lib/nogc_sync_mut/js/engine/parser.spl
---

# JS conformance specs 100%-fail silently: `_run_js` matches `parse_program()` against `Ok`/`Err`, but it returns a plain array

## Summary

`test/03_system/feature/js/es5_conformance_spec.spl` (54 examples),
`es2015_conformance_spec.spl` (38 examples), and `interpreter_vars_spec.spl`
(21 examples) all report **100% failure** under `bin/simple test` — every
single assertion, including trivial ones like `typeof undefined` and `1 + 2`,
fails with `expected nil to equal <X>`. This is unrelated to any actual JS
engine behavior: the shared `_run_js` test helper in all three files has a
structural bug.

Each file's `_run_js` does:
```
val program = parser.parse_program()
match program:
    Ok(stmts): ...
    Err(e): ...
```

But `JsParser.parse_program()` (`src/lib/nogc_sync_mut/js/engine/parser.spl`,
the "subset" engine these specs import via `std.js.engine.parser` /
`std.nogc_sync_mut.js.engine.interpreter`) is declared:
```
me parse_program() -> [JsStatement]:
    js_parse_program_subset(self.source)
```
— a **plain array**, not `Result<[JsStatement], JsError>`. Matching a plain
array against `Ok(...)`/`Err(...)` patterns hits neither arm under the
interpreter (no compile-time exhaustiveness check caught it), so the `match`
silently falls through and `_run_js` returns `nil` for every input,
regardless of source content.

The fix is mechanical — drop the outer match, since `execute()` (which
genuinely returns `BrowserResult<JsValue>`) already provides the Ok/Err
handling:
```
val stmts = parser.parse_program()
val interp = JsInterpreter.new(logger)
val result = interp.execute(stmts)
match result:
    Ok(value): ...
    Err(e): ...
```

## Why not fixed here

Fixing the wrapper is a one-line-shape change per file, but doing so is
expected to immediately surface *separate, unrelated* gaps in this same
"subset" JS engine that are out of scope for lane C8's assigned bug (new-
expression postfix precedence):
- No `class` declaration support in the subset parser at all (`class` is
  parsed as a bare identifier token, discarding the rest of the statement).
- No named `function` declaration support — `function Name(...) {...}` is
  parsed as an anonymous function *expression*; the name is silently
  discarded by `_js_parser_function_expression` (never bound in scope), so
  patterns like `function f(n){...} f(5)` can't resolve `f`.
- No automatic semicolon insertion — the subset parser's top-level statement
  splitter (`_js_parser_split_top_level(source, ";")`) requires an explicit
  top-level `;` between statements; without one, multiple statements collapse
  into a single (usually wrong) expression.

Any of these could make previously-100%-red assertions newly fail for a
*different* reason post-fix, which would need separate triage. Confirmed
(2026-07-18) that fixing `src/lib/nogc_sync_mut/js/engine/parser.spl`'s
`new`-expression handling does not change these suites' failure counts
(54/54, 38/38, 21/21 before and after) — i.e. they are saturated at 100%
failure independent of that fix, consistent with this `_run_js` defect being
the actual blocker, not engine correctness.

## Expected

`_run_js` in all three files reflects `parse_program()`'s real signature so
the suites report genuine pass/fail per assertion instead of a uniform `nil`
wall. A follow-up lane should: (1) apply the mechanical `_run_js` fix in all
three files, (2) triage whatever previously-hidden failures surface (class
support, named function decls, ASI) as separate bugs/lanes.
