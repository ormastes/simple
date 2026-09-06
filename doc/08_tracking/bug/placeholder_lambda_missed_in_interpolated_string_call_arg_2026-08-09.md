# Placeholder-lambda desugar misses interpolated-string call arguments

- **Status:** FIXED (2026-08-09)
- **Severity:** blocker (Stage-3 self-host "blocker 9")
- **Area:** `src/compiler/10.frontend/desugar/placeholder_lambda.spl`
- **Related:** `stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`

## Framing

This is **not** a missing feature. The implicit-lambda placeholder shorthand
(`_`, `_1`, `_2`) has had a real, wired-in pure-Simple desugar pass since
2026-02-25 (`placeholder_lambda.spl`, hooked into `parser_expr.parse_call_arg`,
`parser_stmts`, and `frontend.core_frontend_parse`). It transforms placeholders
into genuine lambda AST nodes *before* HIR construction, and the existing specs
(`test/03_system/feature/usage/{placeholder_lambda,numbered_placeholder,nested_placeholder}_spec.spl`)
cover the ordinary forms.

What was broken is one **narrow, latent edge case**: a placeholder that appears
only inside a **string-template argument**.

## Symptom

Stage 3 phase 3 (HIR lowering) failed closed on 6 call sites:

```
error: HIR lowering error in .../lean_backend.spl:      unresolved name: _
error: HIR lowering error in .../cuda_type_mapper.spl:  unresolved name: _1
```

| file:line | expression |
|---|---|
| `lean_backend.spl:136` | `params.map("({_.0} : {_.1})")` |
| `cuda_type_mapper.spl:159` | `elements.enumerate().map("{self.map_type(_1.1)} _{_1.0}")` |
| `cuda_type_mapper.spl:177`, `:187` | `params.enumerate().map("{self.map_type(_1.1)} p{_1.0}")` |

`lean_backend.spl:205` (`params.map(_.0)`) and `:390` (`params.map(_.1)`) are
**not** affected — plain (non-template) placeholder arguments always worked.
Every failing site is a template argument; no working site is.

## Root cause

Ordering. `parse_call_arg()` runs `transform_placeholder_lambda()` on each
argument at parse time, but a string literal is still **opaque** at that point:
interpolation regions are sub-parsed only *after* the whole module parse, in
`string_interpolation_expand.expand_string_interpolations()`, which promotes
`EXPR_STRING_LIT` → `EXPR_INTERPOLATED_STRING`. So the transform saw no `_` at
all and emitted no lambda; the `_` / `_1` identifiers minted later by that
sub-parse then leaked straight into HIR.

The `EXPR_INTERPOLATED_STRING` arms already present in `placeholder_lambda.spl`
were therefore dead code on this path.

The Rust seed does not hit this because its parser builds the FString parts
inline, before its own `transform_placeholder_lambda` runs — hence Stage 2
(seed-compiled) is green while Stage 3 (pure-Simple) is not.

## Fix

Add a **second pass**, `transform_interpolated_placeholder_args(start_expr)`, run
from `core_frontend_parse()` immediately after `expand_string_interpolations()`.
It walks the expression arena and transforms exactly those call / method-call
arguments that are `EXPR_INTERPOLATED_STRING` **and** contain a placeholder.

Deliberately narrow, to preserve the existing suppression semantics documented
at the top of `placeholder_lambda.spl`: arguments of calls nested *inside* an
interpolation region (e.g. `self.map_type(_1.1)`) are not interpolated strings,
so they are left alone and keep binding to the enclosing template's `_`.

Files:
- `src/compiler/10.frontend/desugar/placeholder_lambda.spl` (new pass)
- `src/compiler/10.frontend/core/frontend.spl` (call it after expansion)
- `src/compiler/10.frontend/desugar/{__init__,mod}.spl` (export)

## Regression coverage

`test/01_unit/compiler/frontend/placeholder_lambda_interpolated_arg_spec.spl`
— 6 examples driving `core_frontend_parse_reset()` directly and asserting on the
resulting arena (no bootstrap required).

- with the pass disabled: `6 total, 2 passed, 4 failed`
- with the pass enabled:  `6 total, 6 passed, 0 failed`

`test/03_system/feature/usage/placeholder_lambda_spec.spl` already carried two
RED examples for exactly this shape ("keeps `_` bound to the outer tuple when a
template slot calls a plain function / a method (type_mapper map_struct
shape)"); they are compiled by the *deployed* binary, so they stay RED until the
self-hosted binary is rebuilt from this source, and are the natural post-rebuild
confirmation.

## Adjacent finding (separate, pre-existing)

Under `native-build`, **any** lambda argument — placeholder or explicit — fails
MIR lowering with `undefined variable: <param>` (`nums.map(\x: x * 2)` fails
identically to `nums.map(_ * 2)`). That is a distinct native-lane defect, not
this bug, and is untouched here.
