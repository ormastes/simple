# Unified Attrs Specification

> <details>

<!-- sdn-diagram:id=unified_attrs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unified_attrs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unified_attrs_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unified_attrs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified Attrs Specification

## Scenarios

### Unified Verification Attributes

#### Contract expressions

#### classifies operators and renders summaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(contracts.ContractExprKind.Forall.is_quantifier()).to_equal(true)
expect(contracts.ContractExprKind.And.is_logical_operator()).to_equal(true)
expect(contracts.ContractExprKind.Ge.is_comparison()).to_equal(true)
expect(contracts.ContractExprKind.Neg.is_arithmetic()).to_equal(true)
expect(contracts.ContractExprKind.Len.is_unary_op()).to_equal(true)
expect(contracts.ContractExprKind.Call.is_variable_reference()).to_equal(false)
expect(contracts.ContractExprKind.Len.to_string()).to_equal("len")
expect(contracts.ContractExprKind.Not.summary()).to_contain("unary op")
```

</details>

#### Function contracts

#### tracks requires, ensures, invariants, and termination

1. var contract = contracts FunctionContract new
2. contracts ContractExpr variable
3. contracts ContractExpr int val
4. contracts ContractExpr result
5. contracts ContractExpr int val
6. contracts ContractExpr variable
7. contracts ContractExpr int val
8. contracts TerminationClause single
9. contract = contract with modifies
   - Expected: contract.has_preconditions() is true
   - Expected: contract.has_postconditions() is true
   - Expected: contract.has_invariants() is true
   - Expected: contract.is_total() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var contract = contracts.FunctionContract.new()
contract = contract.add_precondition(
    contracts.ContractClause.new(
        contracts.ContractExpr.ge(
            contracts.ContractExpr.variable("n"),
            contracts.ContractExpr.int_val(0)
        )
    )
)
contract = contract.add_postcondition(
    contracts.ContractClause.new(
        contracts.ContractExpr.gt(
            contracts.ContractExpr.result(),
            contracts.ContractExpr.int_val(0)
        )
    )
)
contract = contract.add_invariant(
    contracts.ContractClause.new(
        contracts.ContractExpr.ge(
            contracts.ContractExpr.variable("n"),
            contracts.ContractExpr.int_val(0)
        )
    )
)
contract = contract.with_termination(
    contracts.TerminationClause.single(contracts.ContractExpr.variable("n"))
)
contract = contract.with_modifies(contracts.ModifiesClause.nothing())

expect(contract.has_preconditions()).to_equal(true)
expect(contract.has_postconditions()).to_equal(true)
expect(contract.has_invariants()).to_equal(true)
expect(contract.is_total()).to_equal(true)
```

</details>

#### Contract validation

#### rejects impure calls in contracts

1. var contract = contracts FunctionContract new
2. [contracts ContractExpr variable
   - Expected: errors.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var contract = contracts.FunctionContract.new()
contract = contract.add_precondition(
    contracts.ContractClause.new(
        contracts.ContractExpr.call(
            "read_file",
            [contracts.ContractExpr.variable("path")]
        )
    )
)

val errors = contracts.validate_contract(contract)
expect(errors.len()).to_equal(1)
expect(errors[0]).to_contain("pure expression")
```

</details>

#### Class invariants

#### can be marked public

1. contracts ContractExpr variable
2. contracts ContractExpr int val
   - Expected: public_inv.class_name equals `Counter`
   - Expected: public_inv.is_public is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inv = contracts.ClassInvariant.new(
    "Counter",
    contracts.ContractExpr.ge(
        contracts.ContractExpr.variable("value"),
        contracts.ContractExpr.int_val(0)
    )
)
val public_inv = inv.public()

expect(public_inv.class_name).to_equal("Counter")
expect(public_inv.is_public).to_equal(true)
```

</details>

#### Lean contract translation

#### renders invariant and theorem scaffolding

1. [


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inv = lean_contracts.generate_invariant_prop("State", ["x >= 0", "y >= 0"])
val theorem = lean_contracts.LeanTheorem.create(
    "counter_preserves_bounds",
    [("n", "Nat")],
    "n >= 0",
    "rfl"
)

expect(inv.to_lean()).to_contain("def inv_State")
expect(inv.to_lean()).to_contain("x >= 0")
expect(theorem.to_lean()).to_contain("theorem counter_preserves_bounds")
expect(theorem.to_lean()).to_contain("rfl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/unified_attrs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Unified Verification Attributes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
