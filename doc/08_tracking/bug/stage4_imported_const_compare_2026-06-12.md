# Compiled stage4 misevaluates comparisons against imported constants

- **ID:** stage4_imported_const_compare
- **Severity:** P1 (silent logic divergence between interpreted and compiled code)
- **Date:** 2026-06-12
- **Component:** stage4 native pipeline (cranelift lane) — imported `const` resolution in compiled comparisons
- **Status:** OPEN (one call site mitigated with numeric literals)

## Symptom

A comparison against a constant imported from another module (e.g.
`use compiler.core.ast.{EXPR_STRING_LIT}` then `tag == EXPR_STRING_LIT`)
evaluates correctly under seed interpretation but WRONGLY in the compiled
stage4 binary — the branch misfires as if the imported const had a different
value (likely 0/uninitialized at the use site).

## Proven case

`bracket_expr_is_invalid` (src/compiler/10.frontend/core/parser_expr.spl:80)
rejected `m["k"]` string-literal index expressions in COMPILED stage4 only
("index expression cannot be an assignment, comparison, or logical
expression inside []", 71× in src/app/repl/render_adapter.spl). Tracing with
`SIMPLE_TRACE_EXPR_TAGS` showed the expression tag was correctly 3
(EXPR_STRING_LIT) — the comparison against the IMPORTED const constant
misevaluated. Rewriting the same comparisons with numeric literals
(23/24/7/8 / 3) fixed the compiled behavior with no interpreted change.

## Impact

Any lean-frontend (or other compiled-closure) code comparing against
imported consts may silently misbehave in stage4 while testing green
interpreted. This class is invisible to interpreted probes — compiled gates
are required.

Related earlier finding: module-level `val` constants are zero in baremetal
LLVM targets (feedback_baremetal_module_val_zero) — possibly the same
underlying global-init gap surfacing in the cranelift lane.

## Mitigation / next steps

- Mitigated call site: parser_expr.spl:80 uses numeric tags (parser
  convention already favors numeric kinds).
- Audit other imported-const comparisons in src/compiler/10.frontend/
  (EXPR_*/STMT_*/TOK_* imports used in compiled-hot paths).
- Root-cause in the native pipeline: how are cross-module consts
  materialized for cranelift — global load before init?

## Repro

Compiled stage4 check of src/app/repl/render_adapter.spl (pre-mitigation
binary) vs seed-interpreted run of the same parser source on
`m["k"] = "v"` input: interpreted accepts, compiled rejects.
