# Checked converter declaration authority

Requirement: REQ-MC-ANY-001. Status: AUTHORED / UNRUN.
Source: `test/01_unit/compiler/semantics/any_escape/checked_converter_identity_spec.spl`.
Manual authored directly; qualified runner and docgen execution remain UNRUN.

Compiler maintainers use this spec to check a name-authority bypass. A local
`checked_downcast(Any) -> i64` that returns 0 has never checked its input.

| Step | Independent expected result |
|---|---|
| Parse each exact/prefix lookalike with an erased input | No parser or HIR lowering errors |
| Inspect the actual callee | Its resolved ID equals the local function declaration ID |
| Shadow the function with a same-named callable parameter | Callee ID equals parameter ID and differs from function ID |
| Run census and critical analysis | Exactly one probe EscapeCallArg; E-MC-ANY-002; source line 4; Warning/Error respectively |
| Pass an i64 to an identically named concrete function | No findings; callee still resolves |
| Invoke the familiar method on an Any receiver | One probe escape naming the erased receiver; census Warning and critical Error |
| Pass Any to an instance method | Parsed MethodCall, parameter identity preserved, one escaped argument under each profile |
| Pass Any to a declared static method | Parsed MethodCall; StaticMethod owner ID equals the parsed Converter declaration; method ID equals the static binding and parsed checked_downcast declaration, with the expected owner-qualified symbol name; one escaped argument under each profile |
| Replace each erased receiver/argument with a concrete value | No findings under either profile |
| Project the resolved parsed static call to the typed-HIR StaticCall API variant | The separate StaticCall consumer reports one erased argument, with concrete controls clean |

The matrix covers `checked_downcast`, `checked_match`, `type_test`, `is_type`,
`checked_decode_fake`, and `checked_downcast_fake`. Diagnostics are observed from
actual parsed/HIR inputs; matching their spellings in source is not the oracle.

Parsed static-method syntax currently produces `MethodCall` with
`MethodResolution.StaticMethod`. The `StaticCall` scenario explicitly constructs
that separate typed-HIR API variant while preserving the parsed argument and
declaration identities. It does not claim a parsed `StaticCall` producer. No
production producer was found in the bounded frontend/HIR-lowering/method-resolver
inspection. The method cases check this pass's HIR boundary; they do not claim
complete downstream typechecking or code generation of a dynamic Any method.

A canonical converter positive is OPEN. No checked-contract declaration producer
is supplied to this pass. Do not restore a name whitelist, accept an arbitrary
concrete return type, or turn an author annotation into proof of checked behavior.
