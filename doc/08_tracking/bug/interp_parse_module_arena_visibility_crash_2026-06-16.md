# Bug: interpreted `parse_module` + arena decl access crashes (convert_decl_visibility / array-bounds)

## Triage 2026-09-13 — STILL OPEN: could not be reproduced or refuted here
- **measured** — `src/app/cli/query_lint.spl` no longer parses under the Rust seed
  `bin/simple` v1.0.0-rc.1 on Windows: `bin/simple run src/app/cli/query_lint.spl <file>`
  fails with `Unexpected token: expected identifier, found Assign`, so the arena/lint path
  cannot be driven at all from this host.
- **measured** — the file has moved on: line 18 now imports
  `parse_module_silent_checked` / `parser_has_errors` / `parser_set_had_error` and calls
  `parse_module_silent_checked(source, file)` at :697, rather than the bare
  `parse_module` this entry describes.
- **inferred** — the underlying arena/visibility crash is neither confirmed nor cleared.
  Left OPEN.

- **ID:** interp_parse_module_arena_visibility_crash_2026-06-16
- **Severity:** P2 (blocks running any arena-AST lint pass from interpreted app code; blocks reliable-mode R2 wiring and the dormant `_run_ast_lint_passes` suite in the LSP/query path)
- **Area:** interpreter / compiler.core (parse + AST arena, HIR lowering)
- **Status:** open — reproduced across 3 wiring approaches
- **Found during:** reliable-mode P1/R2 (wiring `check_primitive_api_arena` into `query_lint`)

## Summary
When interpreted application code (e.g. `src/app/cli/query_lint.spl` run via
`bin/simple run` / the LSP's `simple src/app/cli/query.spl` path) calls
`compiler.core.parser.parse_module(...)` then accesses the decl arena
(`module_get_decls()`, `decl_tag[idx]`, `decl_get_param_types(idx)`, …), the run aborts with:

```
[INFO] JIT compilation failed, falling back to interpreter:
       HIR lowering error: Unknown variable: decl_get_visibility_text while lowering convert_decl_visibility
error: semantic: array index out of bounds: index is 0 but length is 0
```

The parse/arena machinery does not fully function when invoked indirectly from interpreted
code: the JIT cannot lower `convert_decl_visibility` because `decl_get_visibility_text` is not
available in that closure, and the interpreter fallback then faults on an empty arena array.

## Reproduce
1. Add to `query_lint` (after the text checks, in `_emit_source_lint_diagnostics`):
   `ast_reset(); parse_module(source, file); val d = module_get_decls(); … decl_tag[d[0]] …`
   (or call any `35.semantics/lint` arena check like `check_argument_count` / the new
   `check_primitive_api_arena`).
2. `cp probe.spl src/app/cli/x.spl && bin/simple run src/app/cli/x.spl` where the probe calls
   `_collect_lint_diagnostics_json("fn f(x: i64) -> f64:\n  1.0\n")`.
3. Observe the crash above. Identical across: direct import into query_lint, an own-module
   (`primitive_api_arena.spl`) import, and stripping `@`-attributes before parse.

## Notes / scope
- `bin/simple check query_lint.spl` is **clean** (parse-OK) — this is a runtime/lowering issue,
  not source syntax.
- Standalone `bin/simple run /tmp/x.spl` importing `compiler.core.ast` also can't resolve the
  arena vars (`decl_span not found`) — same family of "compiler-internal arena machinery is not
  fully available to interpreted importers".
- The **CLI `simple lint`** engine (`90.tools/lint`) runs compiled, where `parse_module` works;
  the failure is specific to the *interpreted* invocation the LSP/query path uses.

## Impact
- Reliable-mode R2 is **no longer blocked by this bug** — it was integrated text-based instead
  (`query_lint._emit_primitive_api_text`, reusing `param_tag`'s signature parsers; no
  `parse_module`). The arena module that hit this crash (`primitive_api_arena.spl`) was removed.
- Still real for any **arena-AST** lint driven from interpreted app code: the dead
  `_run_ast_lint_passes` in `query_lint` (zero callers) cannot be activated for the LSP path until
  this is fixed, and any future high-fidelity (typed-Node / arena) primitive or semantic lint on
  the LSP path is gated on it.

## Fix direction
Make `convert_decl_visibility` / `decl_get_visibility_text` (and the arena decl accessors)
resolvable when `parse_module` is driven from interpreted code — i.e. ensure the parser's
internal closure is loaded in the interpreter, or expose a parse entry that returns decls
without triggering visibility lowering. Until then, wire arena lints only on the compiled path
(verify via a bootstrap-built `bin/simple`, not `bin/simple run`).

## Related
- [[r2_primitive_check_draft]] / `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` (R2 —
  resolved text-based; this bug no longer blocks it)
- `src/app/cli/query_lint.spl` → `_run_ast_lint_passes` (the still-dead arena-AST suite this bug blocks)

## Verification note (2026-11-25, release/1.0.0) — crash no longer reproduces

Drove the exact failure shape from interpreted app code at release/1.0.0
HEAD (dfbd7c9d765) with the pinned binary on Windows
(`SIMPLE_LIB=src bin/simple.exe run <probe>`): a probe importing
`compiler.core.parser.{parse_module_silent_checked}` and
`compiler.core.ast.{module_get_decls, decl_tag, decl_get_visibility_text}`
parsed `fn f(x: i64) -> f64:\n    1.0\n` and walked the decl arena.

Result: `PARSE_FAILED=false`, `DECL_COUNT=1`,
`DECL tag=1 vis=decl_get_visibility_text(...)` returns `private` —
no `HIR lowering error: Unknown variable: decl_get_visibility_text while
lowering convert_decl_visibility`, no `array index out of bounds: index
is 0 but length is 0`. The 2026-09-13 triage blocker (`query_lint.spl`
not parsing under the seed) is also gone: `query_lint.spl` now imports
and calls `parse_module_silent_checked` (:722) with `module_get_decls()`
(:731), and both the parse and the arena accessors work from interpreted
code, so the arena/lint path can be driven from this host.

The interpreter-path crash this entry tracks does not reproduce with the
pinned v1.0.0-rc.1 seed against the current tree. The status header
("open — reproduced across 3 wiring approaches") is stale.

**Status:** resolved (crash signature verified absent at tip via direct
interpreted parse_module + arena-access probe).
