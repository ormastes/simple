# Shared HIR literal constant owner and MIR compatibility

Requirement: REQ-MC-003. Executable spec: `test/01_unit/compiler/mir/hir_literal_constant_compat_spec.spl`.

Status: authored review manual; execution and SPipe generation **UNRUN**. Expected observations are not runtime evidence.

| Action | Assertion oracle |
|---|---|
| Fold each accepted integer binary operator through the shared HIR owner and retained MIR wrapper | Both return the handwritten expected integer |
| Fold nested arithmetic, Neg and BitNot | Nested20, inverted-2 and negated inversion2 retain their values |
| Divide or take modulo by zero | Both APIs return unavailable |
| Fold bool, string, float and FloatLexeme constants | Both preserve the corresponding kind; exact lexeme bytes survive |
| Negate FloatLexeme values with no sign, plus sign and minus sign | Toggle one sign textually without converting to f64 |
| Negate float zero | Both float results retain negative zero, observed through the reciprocal sign |
| Fold variables, named variables, calls, casts, comparisons and Pow | Both APIs remain unavailable |
| Fold boolean Not, an interpolated string or mixed float/integer arithmetic | Both APIs remain unavailable |

These scenarios protect a mechanical extraction of MIR's existing literal subset. They do not authorize the wider general ConstEvaluator or establish checked/wrapping behavior for overflow, MIN/-1 or invalid shift counts. Native compatibility, runtime transport, timing and RSS remain unqualified.
