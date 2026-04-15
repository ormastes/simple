# Math Language Specification

Math language features for Simple:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #2200-2205 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/math_language_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Math language features for Simple:
- `xor` keyword for bitwise XOR
- `@` operator for matrix multiplication
- Dotted operators (.+, .-, .*, ./, .^) for broadcasting
- `m{}` math blocks with `^` power operator

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/math_language/result.json` |

## Scenarios

- computes bitwise XOR of two integers
- returns identity when XOR with 0
- returns 0 when XOR with itself
- has lower precedence than and
- has higher precedence than or
- parses @ as matrix multiply
- binds tighter than addition
- binds looser than multiplication
- parses .+ as broadcast add
- parses .- as broadcast sub
- parses .* as broadcast mul
- parses ./ as broadcast div
- parses .^ as broadcast pow
- allows ^ as power inside math block
- computes quadratic expression
- handles nested exponentiation
- computes distance formula
- mixes ^ and ** equivalently
- handles nested braces in math block
- works outside math blocks
- works inside math blocks
- is right-associative
