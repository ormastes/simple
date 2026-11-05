# JS engine: es2015 conformance spec was silently broken; parser gaps now exposed
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-05
**Spec:** `test/03_system/feature/js/es2015_conformance_spec.spl`
**Status:** open — 13 genuine failures now visible (25 pass)

## What happened

During the Modern-SSpec port of the es2015 conformance spec, its `_run_js`
helper turned out to have a compile-time semantic error (`Logger(level: ...)` —
`Logger` has no `level` field; plus a stale `Ok`/`Err` match on
`parser.parse_program()`, which now returns `[JsStatement]` directly). The spec
had therefore been failing 38/38 at compile time and never truly exercised the
engine. The helper is fixed; the suite now runs for real.

## Exposed engine gaps (pre-existing, not port artifacts)

`js_parse_program_subset` (nogc_sync_mut JS engine) only recognizes `var`
declarations (confirmed by source inspection). Failing ES2015 features:

- `let` / `const`
- template literals
- destructuring
- spread
- classes
- `for...of` / `for...in`

Passing: array higher-order methods (map/filter/reduce/some/every/includes),
nullish coalescing — 25 scenarios.

## Scope note

The JS engine is a real product surface, not internal scripting: it executes
third-party JavaScript for the browser stack
(`src/lib/gc_async_mut/web/browser_session.spl` runs inline `<script>` JS) and
the JS runtime CLI (`src/app/js/main.spl`). The engine itself is written in
Simple (`src/lib/common/js/`). So these gaps are genuine browser script-support
limitations — most real web pages use `let`/`const`.

## Next steps

- Extend `js_parse_program_subset` per feature above, or explicitly scope the
  engine's supported subset and mark unsupported scenarios as planned features
  (needs approval — never silently skip).
- Related audit lesson: the interpreter file-summary greenwash bug
  (`doc/08_tracking/bug/test_runner_interpreter_file_summary_greenwash_2026-07-03.md`)
  is how a 38/38-failing spec stayed invisible.

## Resolution progress — 2026-11-05 (work/libbug-std-jses2015-20261105)

Fixed in `src/lib/nogc_sync_mut/js/engine/parser.spl` (all runtime support
already existed in the interpreter; only the subset parser did not produce
these AST nodes):

- `let` / `const` declarations → `JsStatement.LetDecl` / `ConstDecl`
  (`_js_parser_var_decl_kind` generalizes the old `var `-only arm).
- Object/array destructuring in var/let/const declarations →
  `JsStatement.DestructVarDecl` with `ObjectPattern`/`ArrayPattern`
  (`_js_parser_object_pattern`, `_js_parser_array_pattern`).
- Template literals → `JsExpression.TemplateLiteral`
  (`_js_parser_template_literal_at`, `_js_parser_template_end`; backtick
  handling added to `_js_parser_primary_at`/`_js_parser_primary_end`).
- Array spread `[...a, 3]` → `SpreadElement` array elements (handled by the
  pre-existing spread-aware `eval_array`).
- Call spread `f(...a)` → parser desugar to `f.apply(null, [...])` (the
  generic call path evaluates each arg once and cannot expand spreads).
- Class declarations `class C { constructor() {...} m() {...} }` →
  `JsStatement.ClassDecl` (`_js_parser_class_statement` + a `class` arm in
  `_js_parser_leading_construct_end`); an empty constructor is synthesized
  when absent because `exec_class_decl` only registers the class when the
  constructor is a `FnDecl`.

Spec-side fix in `test/03_system/feature/js/es2015_conformance_spec.spl`:
restored the dropped `js_evaluates` helper (the Modern-SSpec port referenced
it without defining it — 38/38 "failures" were `semantic: function
js_evaluates not found`), fixed the `JsLogger` construction to
`JsLogger.new(name, level)`, and escaped the JS `${...}` template holes as
`${{...}}` so Simple's own brace interpolation passes them through verbatim.

Results on the release/1.0.0 worktree: es2015 conformance 0/38 → 38/38
(interpreter mode, phase-1 seed binary). No regressions: es5 conformance
(45/54), node_api (57/275), node_process_next_tick (0/2), and
test/01_unit/lib/js (48/61) are per-case identical to the pre-change
baseline; interpreter_vars improved 14/21 → 16/21 (let/const cases).

Remaining open engine gaps (not covered by this spec, observed during the
work): node_api/node_process_next_tick/es5 failures are pre-existing and
unrelated to the parser; the `src/lib/common/js/engine/parser.spl` "full"
parser and the `src/lib/nogc_sync_mut/js/engine/lexer.spl` stub were not
touched.

