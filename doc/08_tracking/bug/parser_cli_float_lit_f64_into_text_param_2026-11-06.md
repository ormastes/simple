# parser_cli passes an f64 to expr_float_lit(value: text) — cranelift call-ABI reject (2026-11-06)

**Status:** fix-implemented-verification-pending (2026-11-06; closes when a Stage 2 `compiler_cli_build` row passes)

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

## Fix (2026-11-06)

`parser_cli.spl:226` now passes the token text: `expr_float_lit(fval, 0)`. The callee stores
the literal as text (`expr_f_val[idx] = value`, `expr_text_set(idx, "F", value)`), and the
primary-expression parser already calls it that way (`_ParserPrimary/primary_expr.spl:457`), so
the caller was wrong, not the signature.

Red -> green, run-10 Stage 2 compiler (sha256 `43f9a6fc68ac232f...`), the phase-C
`compiler_cli_build` argv shape (`native-build <entry> --backend=cranelift --low-memory
--threads 2`, `SIMPLE_FILE_WORKERS=0 SIMPLE_BOOTSTRAP=1`, 16G cgroup), entry
`src/compiler/10.frontend/core/parser_cli.spl`:

- before: `[cranelift] E-BACKEND-CRANELIFT-CALL-ABI: call to ...expr_float_lit in
  ...parse_cli_option_value: arg 0 is f64 but the callee declares i64`, worker SIGABRT.
- after: no CALL-ABI error; every module reaches codegen and the build stops only at the
  link (`undefined symbol: __simple_main`), expected for an entry with no `main`.

## Open side findings (not fixed here)

- The type checker admitted an `f64` argument for a `text` parameter; only the backend
  call-ABI check caught it.
- After the CALL-ABI error the worker died with SIGABRT (-134) and the driver reported
  "worker terminated with signal 6 ... NOT a compile failure" plus an attributed ICE, i.e.
  a genuine compile error was classified as a worker crash.
