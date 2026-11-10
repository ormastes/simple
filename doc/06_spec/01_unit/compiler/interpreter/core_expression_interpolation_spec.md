# Core expression interpolation

Source: `test/01_unit/compiler/interpreter/core_expression_interpolation_spec.spl`.
Requirement: `REQ-COMPILER-INTERPRETER-001`.

This authored manual describes five executable scenarios. Runtime execution
and generated-doc validation are pending a usable self-hosted full CLI; no
test count or runtime PASS is claimed.

The tests assemble source text using brace character codes, then call the
actual core expression interpreter. This prevents the outer test runner from
interpolating the fixture before the product interpreter sees it.

1. Evaluate arithmetic and multiple interpolation regions. Expect `sum=5`
   and `2/12`, not literal brace expressions.
2. Bind a lambda parameter at runtime and interpolate it through the expression
   entry point. Compare with the module entry point binding the same value;
   both must return `value=7` without evaluation errors.
3. Evaluate doubled-brace escapes containing an undefined identifier. Expect
   one pair of literal braces, without looking up the identifier.
4. Preserve raw interpolation-looking text and ordinary brace-free text.
5. Keep a malformed CSS-shaped region literal while evaluating its valid
   arithmetic neighbor, using the existing region-only interpolation rule.

Run with a proven self-hosted test runner:

```
<runtime> test test/01_unit/compiler/interpreter/core_expression_interpolation_spec.spl --mode=interpreter
```

The original Stage4 defect additionally requires a fresh full CLI running
`string_interpolation_spec.spl` and the original `run` fixture with seed
delegation impossible. Passing this focused API spec alone cannot close that
original qualification requirement.
