# parser_cli passes an f64 to expr_float_lit(value: text) — cranelift call-ABI reject (2026-11-06)

**Status:** open

Found while verifying `mir_generic_trait_bound_receiver_unresolved_2026-11-06`: a Stage 2 compiler
built from release/1.0.0 + that fix lowered the whole `tldr_table_fill_v1.spl` closure through MIR
(`[mir] 285/285`), then the cranelift backend rejected the module set:

    [cranelift] E-BACKEND-CRANELIFT-CALL-ABI: call to compiler.frontend.core._AstExpr.nodes.expr_float_lit
      in compiler.frontend.core.parser_cli.parse_cli_option_value: arg 0 is f64 but the callee declares i64

Source: `src/compiler/10.frontend/core/parser_cli.spl:226`
`val fexpr = expr_float_lit(fval.to_float(), 0)` while
`src/compiler/10.frontend/core/_AstExpr/nodes.spl:601` declares `fn expr_float_lit(value: text, span_id: i64)`.
The caller converts the text to a float and the callee wants the text. Expected to be the next
`compiler_cli_build` blocker after the generic-receiver MIR fix. Not caused by that fix (non-generic
callee, untouched path); the run-10 Stage 2 stopped earlier in MIR and never reached the backend.

Likely fix: pass `fval` (the text) instead of `fval.to_float()`; also ask why the type checker
admitted an f64 argument for a `text` parameter.
