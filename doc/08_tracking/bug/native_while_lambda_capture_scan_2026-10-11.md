# While expressions block native callback closure conversion

The unchanged `while_body_scope_spec.spl` registered through real `std.spec`
emits `E-MIR-EXPR-Lambda` with experimental native producer c486d76512b3
(source eecd0d7c0de). LLVM compilation nevertheless links an artifact; both
enumeration and execution then terminate with signal 11 after `owner_begin`,
before any cases or assertions are recorded. This is a failure, not a skip.

`lower_lambda_value` already lifts callbacks. Its three cooperating scans omit
`HirExprKind.While`: capture detection conservatively returns true, supported-
shape validation returns false, and free-variable collection omits its contents.
The lift consequently returns nil for the original callback.

The repair traverses the condition with the enclosing bindings and traverses
the body with body-local declarations added. Body declarations do not affect
the condition or enclosing scope. It extends the existing conversion only.

MIR regressions cover a no-capture callback preserving the outer `shadow = 99`
and a callback capturing `limit` in the condition plus `step` in its body,
where a body-local `limit` shadows the capture. The standalone native fixture
checks the observable results 101 and 10. Runtime verification is pending a
rebuilt native producer; the current frozen experimental producer is unchanged.

Evidence: `/home/yoon/dev/phase2-six-results-20261011/permanent-repair/normal-firstfile/llvm-positive/`.
The original std.spec positive and intentional negative must pass before the
restricted adapter can be removed. Full compiler/core checks remain pending.
