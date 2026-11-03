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

Expected: a `Literal` pattern carrying the existing `FloatLexeme` expression
(which HIR then desugars to an if-chain via
`pattern_is_mir_native == false`), so a partial float match is reported and a
float arm only fires on equal values. `convert_flat_expr` represents source
float literals as `ExprKind.FloatLexeme`; the frontend bridge must preserve that
lexeme rather than converting it to a different literal kind.

Status: open. Out of scope for the value-match lane; its spec exercises the
float class through a float scrutinee with int-literal arms instead.

### 2026-11-02 — frontend bridge repair and bounded diagnostic

`convert_flat_pattern` now accepts `EXPR_FLOAT_LIT` in its literal branch and
uses the existing `convert_flat_expr` path. This preserves top-level float
patterns and float sub-patterns in enum payloads. The direct-owner diagnostic
compared the same fail-fast fixture against the original release source and the
patched owner: the original failed on `1.5` as a non-literal pattern, while the
patched source passed six assertions for `1.5`, unary `-1.5`, the method-form
`Shape.Circle(1.0)` payload, and the explicit wildcard fallback.

Evidence and complete logs:
`doc/08_tracking/bug/evidence/float_literal_pattern_2026_11_02/receipt.sdn`.
The run used an unadmitted Windows Rust seed in interpreter mode. It establishes
the frontend bridge owner only; it does not establish HIR, MIR, native, or
standard SSpec execution. The added HIR regression in
`test/01_unit/compiler/hir/float_literal_pattern_bridge_spec.spl` remains
unexecuted. Keep this bug OPEN until that HIR regression runs and a real float
match verifies both equality selection and non-exhaustive handling.
