# Vhdl Dim Constraints Specification

> 1. ok solver add

<!-- sdn-diagram:id=vhdl_dim_constraints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vhdl_dim_constraints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vhdl_dim_constraints_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vhdl_dim_constraints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Dim Constraints Specification

## Scenarios

### Vhdl Dim Constraints

#### accepts and rejects width matches

1. ok solver add
   - Expected: ok_solver.solve().is_ok() is true
2. bad solver add
   - Expected: bad_result.is_err() is true
   - Expected: bad_errors.len() equals `1`
   - Expected: bad_errors[0].error_code equals `E0700`
   - Expected: bad_errors[0].kind equals `DimErrorKind.WidthMismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok_solver = DimSolver.new()
ok_solver.add(DimConstraint.WidthMatch(lit(32), lit(32), "<=", test_span()))
expect(ok_solver.solve().is_ok()).to_equal(true)

val bad_solver = DimSolver.new()
bad_solver.add(DimConstraint.WidthMatch(lit(8), lit(16), "<=", test_span()))
val bad_result = bad_solver.solve()

expect(bad_result.is_err()).to_equal(true)
val bad_errors = bad_result.unwrap_err()
expect(bad_errors.len()).to_equal(1)
expect(bad_errors[0].error_code).to_equal("E0700")
expect(bad_errors[0].kind).to_equal(DimErrorKind.WidthMismatch)
```

</details>

#### checks width safety for addition and multiplication

1. add ok add
   - Expected: add_ok.solve().is_ok() is true
2. add bad add
   - Expected: add_bad_result.is_err() is true
   - Expected: add_bad_result.unwrap_err()[0].error_code equals `E0701`
   - Expected: add_bad_result.unwrap_err()[0].kind equals `DimErrorKind.WidthOverflow`
3. mul bad add
   - Expected: mul_bad.solve().is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add_ok = DimSolver.new()
add_ok.add(DimConstraint.WidthSafe([lit(16), lit(16)], "+", lit(17), test_span()))
expect(add_ok.solve().is_ok()).to_equal(true)

val add_bad = DimSolver.new()
add_bad.add(DimConstraint.WidthSafe([lit(16), lit(16)], "+", lit(16), test_span()))
val add_bad_result = add_bad.solve()
expect(add_bad_result.is_err()).to_equal(true)
expect(add_bad_result.unwrap_err()[0].error_code).to_equal("E0701")
expect(add_bad_result.unwrap_err()[0].kind).to_equal(DimErrorKind.WidthOverflow)

val mul_bad = DimSolver.new()
mul_bad.add(DimConstraint.WidthSafe([lit(32), lit(32)], "*", lit(32), test_span()))
expect(mul_bad.solve().is_err()).to_equal(true)
```

</details>

<details>
<summary>Advanced: accepts bounded loops within the limit and rejects unbounded ones</summary>

#### accepts bounded loops within the limit and rejects unbounded ones

1. ok solver add
   - Expected: ok_solver.solve().is_ok() is true
2. bad solver add
   - Expected: bad_result.is_err() is true
   - Expected: bad_result.unwrap_err()[0].error_code equals `E0730`
   - Expected: bad_result.unwrap_err()[0].kind equals `DimErrorKind.UnboundedLoop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok_solver = DimSolver.new()
ok_solver.add(DimConstraint.BoundedLoop(lit(256), 1024, test_span()))
expect(ok_solver.solve().is_ok()).to_equal(true)

val bad_solver = DimSolver.new()
bad_solver.add(DimConstraint.BoundedLoop(lit(2048), 1024, test_span()))
val bad_result = bad_solver.solve()

expect(bad_result.is_err()).to_equal(true)
expect(bad_result.unwrap_err()[0].error_code).to_equal("E0730")
expect(bad_result.unwrap_err()[0].kind).to_equal(DimErrorKind.UnboundedLoop)
```

</details>


</details>

#### checks valid ranges in both directions

1. ok solver add
   - Expected: ok_solver.solve().is_ok() is true
2. bad solver add
   - Expected: bad_result.is_err() is true
   - Expected: bad_result.unwrap_err()[0].error_code equals `E0740`
   - Expected: bad_result.unwrap_err()[0].kind equals `DimErrorKind.InvalidRange`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok_solver = DimSolver.new()
ok_solver.add(DimConstraint.ValidRange(lit(7), lit(0), test_span()))
expect(ok_solver.solve().is_ok()).to_equal(true)

val bad_solver = DimSolver.new()
bad_solver.add(DimConstraint.ValidRange(lit(3), lit(7), test_span()))
val bad_result = bad_solver.solve()

expect(bad_result.is_err()).to_equal(true)
expect(bad_result.unwrap_err()[0].error_code).to_equal("E0740")
expect(bad_result.unwrap_err()[0].kind).to_equal(DimErrorKind.InvalidRange)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/vhdl_dim_constraints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vhdl Dim Constraints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
