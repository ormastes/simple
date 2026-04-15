# Floor Division (.fdiv) Method

The `.fdiv()` method provides floor division functionality, replacing the old `//` operator

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | OP-FDIV |
| Category | Operators \| Arithmetic |
| Status | Implemented |
| Source | `test/feature/usage/floor_division_fdiv_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 53 |
| Active scenarios | 53 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

The `.fdiv()` method provides floor division functionality, replacing the old `//` operator
which is now used for parallel execution.

Floor division divides two numbers and rounds down (towards negative infinity), unlike
truncating division which rounds towards zero.

## Migration from // Operator

**Old syntax (deprecated):**
```simple
val result = 7 // 2  # Floor division (old)
```

**New syntax:**
```simple
val result = 7.fdiv(2)  # Floor division (new)
```

## Mathematical Definition

Floor division: ⌊a/b⌋ (always rounds towards negative infinity)

Properties:
- `a = b * a.fdiv(b) + a % b` (division algorithm)
- `a.fdiv(b)` has same sign as `a / b` when positive
- `a.fdiv(b)` rounds down for negative results

## Examples

```simple
7.fdiv(2)    # → 3
10.fdiv(3)   # → 3

(-7).fdiv(2)   # → -4 (not -3)
7.fdiv(-2)     # → -4 (not -3)
(-7).fdiv(-2)  # → 3

7.5.fdiv(2.0)    # → 3.0
(-7.5).fdiv(2.0) # → -4.0
```

## Comparison with Other Division

| Operation | 7 / 2 | -7 / 2 | 7 / -2 | -7 / -2 |
|-----------|-------|--------|--------|---------|
| Regular `/` | 3 | -3 | -3 | 3 |
| Floor `.fdiv()` | 3 | -4 | -4 | 3 |
| Truncate `.trunc()` | 3 | -3 | -3 | 3 |

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/floor_division_fdiv/result.json` |

## Scenarios

- divides evenly
- divides with remainder
- divides with large remainder
- divides exactly
- divides small by large
- divides one by one
- divides large numbers
- divides negative by positive (rounds down)
- divides positive by negative (rounds down)
- divides negative by negative (positive result)
- divides negative evenly
- handles negative dividend with remainder
- handles negative divisor with remainder
- handles both negative with remainder
- divides zero by positive
- divides zero by negative
- handles one divided by itself
- handles negative one by one
- handles one by negative one
- satisfies division algorithm for positive numbers
- satisfies division algorithm for negative dividend
- satisfies division algorithm for negative divisor
- satisfies division algorithm for both negative
- divides evenly
- divides with fractional result
- divides small by large
- divides with small quotient
- divides exactly at boundary
- divides fractional by integer
- divides negative by positive
- divides positive by negative
- divides negative by negative
- handles negative fractional dividend
- handles negative fractional divisor
- handles division by very small number
- handles very large result
- handles very large value divided by finite
- handles very small value as divisor
- handles zero fdiv positive
- matches regular division for positive exact division
- differs from regular division when remainder exists
- differs for negative dividend
- differs for negative divisor
- calculates number of pages needed
- calculates array chunk count
- calculates time in hours
- calculates grid coordinates
- rounds negative temperatures to day boundary
- always produces result <= regular division for negative
- always rounds down for fractional floats
- is idempotent for exact division
- matches math block floor division for positive
- matches math block floor division for negative
