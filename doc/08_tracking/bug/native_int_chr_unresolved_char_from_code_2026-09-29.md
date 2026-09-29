# Native `i64.chr()` emitted an unresolved `char_from_code`

Status: call-site repair present; native lowering defect remains open.

The expanded Target 6 native integration closure linked all runtime symbols
except internal `char_from_code`. `nm` located the undefined reference in the
object for `compiler.frontend.core.interpreter._EvalOps.call_method_eval`, at
its `n.chr()` branch. The stage compiler emitted a bare symbol without a
linked implementation. That branch now calls the existing
`std.common.string_core.char_from_code_inline` after its existing Unicode
scalar validation; the next native build linked successfully.

Fix the native lowering of `i64.chr()` itself and add a focused native
Unicode scalar regression, then consider restoring the compact expression.
