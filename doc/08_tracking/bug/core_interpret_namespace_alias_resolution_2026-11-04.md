# core_interpret: `ns.member(...)` on a `use mod as ns` namespace fails

Spec: test/01_unit/compiler/interpreter/module_namespace_alias_runtime_spec.spl (5/6 failed).

Symptom: `eval_has_error()` true, `eval_get_error()` = `undefined variable: ns`.

Root cause: the parser builds `ns.orig()` / `math.Vec3Math78(...)` as EXPR_METHOD_CALL.
The namespace registered by the loader (`func_module_namespace_register`) was only
consulted in the EXPR_CALL field-access path (eval_calls.spl) and field access, never in
`eval_method_call` (src/compiler/10.frontend/core/interpreter/_EvalOps/call_method_eval.spl),
which evaluated the receiver `ns` as a variable.

Fix: in `eval_method_call`, when the receiver is an identifier registered as a caller
namespace, resolve the member function (or struct constructor) through the namespace first.

Result: spec 6/6; 16 related interpreter module/import/namespace specs unchanged (all pass).
