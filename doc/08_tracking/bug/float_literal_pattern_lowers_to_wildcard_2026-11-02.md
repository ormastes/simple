# Float-literal match pattern is lowered to a wildcard

Found by lane exhaustive-value-match (2026-11-02) while writing
`test/03_system/app/compiler/feature/exhaustive_value_match_spec.spl`.

`match s:` over an `f64` with `case 1.5:` reaches HIR as
`HirPatternKind.Wildcard` (checked by walking the lowered HIR of
`fn f(s: f64) -> i64: val x = match s: case 1.5: 10; x`). `HirLowering.lower_pattern`
is faithful (`Literal -> HirPatternKind.Literal`), so the literal is already a
wildcard when it leaves the frontend pattern conversion (`convert_flat_pattern`
in 10.frontend). Consequence: the arm matches EVERY value, and the match looks
exhaustive to every later pass, including E-MATCH-NONEXHAUSTIVE-VALUE. Same for
a float sub-pattern in an enum payload (`Shape.Circle(1.0)`).

Expected: `Literal(FloatLit)` (which HIR then desugars to an if-chain via
`pattern_is_mir_native == false`), so a partial float match is reported and a
float arm only fires on equal values.

Status: open. Out of scope for the value-match lane; its spec exercises the
float class through a float scrutinee with int-literal arms instead.
