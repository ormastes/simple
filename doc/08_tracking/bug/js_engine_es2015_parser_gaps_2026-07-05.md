# JS engine: es2015 conformance spec was silently broken; parser gaps now exposed

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
