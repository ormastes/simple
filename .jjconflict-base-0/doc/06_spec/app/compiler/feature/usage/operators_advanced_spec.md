# Advanced Operators Specification

Tests advanced operators and language features including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OP-ADV-001 to #OP-ADV-030 |
| Category | Language \| Operators |
| Status | Implemented |
| Source | `test/feature/usage/operators_advanced_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests advanced operators and language features including:
- Mutability control (let, let mut, var, const, static)
- Lambda expressions
- String operations
- Array and dict methods
- Bitwise operators
- Comparison and logical operators
- Power and floor division
- In operator
- Symbols

## Syntax

```simple
let x = 10       # immutable
let mut y = 10   # mutable with let mut
var z = 10       # mutable with var
const MAX = 100  # constant
static counter = 0  # static variable

val a = 12 & 10    # bitwise AND
val b = 2 ** 10    # power
val c = 7.fdiv(2)  # floor division (// is now parallel operator)
val d = "ell" in "hello"  # in operator
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/operators_advanced/result.json` |

## Scenarios

- let is immutable
- var is mutable
- var in loop
- const declaration
- const with arithmetic
- const with type annotation
- static variable
- basic lambda
- lambda with multiple params
- lambda as higher-order
- string length
- string concatenation
- string interpolation
- array length
- dict length
- dict keys
- dict values
- dict contains_key
- bitwise AND
- bitwise OR
- bitwise XOR
- left shift
- right shift
- bitwise NOT
- less than
- greater than
- less than or equal
- greater than or equal
- equal
- not equal
- and operator
- or operator
- not operator
- power of zero
- power of one
- power of three
- power of ten
- three to fourth
- positive floor division
- another floor division
- negative floor division
- exact division
- in array present
- in array absent
- in string present
- in string absent
- factorial
- nested arrays
- nested structs
- early return based on condition
- destructures tuple
- symbol comparison
