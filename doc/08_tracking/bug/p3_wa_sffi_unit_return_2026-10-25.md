# P3 WA: E-SFFI-016 on `-> ()` function with `return ()` (`WA-P3-sffi-unit`)

`me emit_pending_finally_for_transfer() -> ():` has an early `return ()` and falls through on a
statement; E-SFFI-016 (declaration_lowering.spl) counts `return ()` as a value return, so the fall-through
is "missing return in non-unit function".

Real fix: treat `()` as unit both in the annotation and in `return ()`.

WA site: src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl — annotation dropped, bare `return`.
