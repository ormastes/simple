# Compiled stage4 misevaluates comparisons against imported constants

- **ID:** stage4_imported_const_compare
- **Severity:** P1 (silent logic divergence between interpreted and compiled code)
- **Date:** 2026-06-12
- **Component:** stage4 native pipeline (cranelift lane) — imported `const` resolution in compiled comparisons
- **Status:** resolved (2026-06-14)

## Resolution (2026-06-14)

`const X = 3` without a type annotation was lowered with `TypeId::ANY` in both
the defining-module pass (`hir/lower/module_lowering/module_pass.rs`) and the
import-loader pass (`hir/lower/import_loader.rs`). On an `ANY`-typed operand the
equality lowering routed through `rt_native_eq` and applied `BoxInt` (shift-left
by 3) to only the non-ANY side, comparing `rt_native_eq(24, 3)` instead of
`(3, 3)`. Fix: infer the literal type for unannotated consts (`Integer`→`I64`,
`String`/`FString`→`STRING`) in both passes. Verified: cross-module and local
`check_tag(3)`→1, `check_tag(2)`→2, `check_tag(99)`→0. Requires seed rebuild.

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

## 2026-06-13 investigation — what this bug is and is NOT

A 2026-06-13 probe initially looked related but turned out to be a **DISTINCT
bug**, now filed separately as
`jit_string_method_on_var_receiver_folds_2026-06-13.md`:

- That bug: a **string method** on a local/global string **variable**
  (`TABLE.char_at(0)`) returns empty in JIT because the receiver is folded into
  the call name and never loaded. `__module_init` DOES run and materialize the
  string; it is NOT a global-init ordering problem, and local `val`s fail too
  (not module-specific). Workaround: route through a `text` param.
- THIS bug (`stage4_imported_const_compare`): a **comparison** `tag ==
  IMPORTED_CONST` misevaluates in compiled stage4. A scalar repro
  (`val N: i64 = 3; print(3 == N)`) currently evaluates **correctly** in JIT, so
  the original symptom may be specific to the self-hosted stage4 binary and/or
  cross-module (imported) consts under a shared-prelude closure — still needs a
  minimal repro that reproduces outside the full stage4 build. Audit imported
  `EXPR_*`/`STMT_*`/`TOK_*` const comparisons in `src/compiler/10.frontend/`.
