# Cranelift AOT rejects cross-module read of a private module static (accessors)

Symptom: Phase-3 native-build fails unit `compiler.frontend.core._AstExpr.accessors` with
`backend session AOT result rejected: <enum@...>` (enum payload lost by to_text(); fixed in
simple-boot-p2shard 5a5513e2ca0 via `backend_session_authority_error_text_v2`).

Real cause (build.log, stdout just before the error):
`[cranelift] imported non-public module static 'compiler_frontend_core__AstExpr_nodes__expr_tag' requires visibility-preserving accessor support`
Emitted at src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:387 (declare_module_statics).
accessors.spl:136 and :184 read `expr_tag.len()` directly (an earlier workaround that avoids a
cross-module i64 return), but `var expr_tag` in nodes.spl:89 is private. See
cranelift_aot_accessor_visibility_2026-10-11.md: only Public statics get an address accessor.

Second, separate failure in the same build: unit `lib.common.math.math` fails with
`unsupported module static 'lib_common_math_math__MATH_PI' (non-scalar type or non-const init)`
(adapter:382; `pub val MATH_PI: f64` -- f64 static init not supported). Not addressed here.

Workaround: `pub var expr_tag` in nodes.spl (tagged `@workaround`). Real fix: the backend should
support visibility-preserving accessors for non-public statics (blocked on AOT define-function
linkage, per the 2026-10-11 doc). Unverified: no rebuild was run.
