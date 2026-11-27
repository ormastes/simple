# Cranelift AOT rejects cross-module read of private expr_tag static

Symptom: Phase-3 native-build fails unit `compiler.frontend.core._AstExpr.accessors`:
`[cranelift] imported non-public module static '...expr_tag' requires visibility-preserving accessor support`
(`cranelift_codegen_adapter.spl` declare_module_statics).

## Language rule decision
`doc/07_guide/quick_reference/syntax_quick_reference.md` (Visibility): private = same file only.
Reading a private static from accessors.spl (a different file) is therefore ILLEGAL; the
backend rejection is correct, not a backend gap. Implementing hidden/private accessors is
also blocked on AOT define-function linkage (cranelift_aot_accessor_visibility_2026-10-11.md).

## Fix (permanent, source side)
The ten pools (`expr_tag/span/i_val/f_val/s_val/left/right/extra/args/stmts`) are
`export`ed by `core/__init__.spl:269` and read by accessors, collection_desugar,
placeholder_lambda, primary_expr, module_state. They are public API, so they are now
declared `pub var` in `_AstExpr/nodes.spl`. Internal-only pools stay private (0 outside readers).
This is the real declaration, not a workaround: no `@workaround` tag; the interim
`pub var expr_tag` commit 8ab7cd693d8 (simple-boot-adhoc) is superseded and extended to siblings,
which would have failed identically once reached.

## Verification
Spec: test/01_unit/compiler/ast_expr_pool_visibility_spec.spl (source-shape; NOT executed).
Not verified: native-build with this change (no Stage 2 rebuild allowed).
Separate, unaddressed: `MATH_PI` f64 static unsupported (adapter:382).
