# Bug: interpreted `parse_module` + arena decl access crashes (convert_decl_visibility / array-bounds)

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
- Reliable-mode R2: the primitive check module (`compiler.semantics.lint.primitive_api_arena`,
  landed) cannot be wired into the LSP/build diagnostic path until this is fixed.
- The existing `_run_ast_lint_passes` in `query_lint` is already dead (zero callers); this bug is
  why it cannot simply be activated for the LSP path either.

## Fix direction
Make `convert_decl_visibility` / `decl_get_visibility_text` (and the arena decl accessors)
resolvable when `parse_module` is driven from interpreted code — i.e. ensure the parser's
internal closure is loaded in the interpreter, or expose a parse entry that returns decls
without triggering visibility lowering. Until then, wire arena lints only on the compiled path
(verify via a bootstrap-built `bin/simple`, not `bin/simple run`).

## Related
- [[r2_primitive_check_draft]] / `doc/03_plan/compiler/reliable_mode/reliable_mode_plan.md` (R2)
- `src/compiler/35.semantics/lint/primitive_api_arena.spl` (the blocked-on-wiring check)
