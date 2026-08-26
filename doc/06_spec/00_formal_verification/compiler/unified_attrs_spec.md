# Unified Attrs Specification

> Tests covering Unified Verification Attributes.

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

- classify contract operators and render summaries
   - Expected: contracts.ContractExprKind.Forall.is_quantifier() is true
   - Expected: contracts.ContractExprKind.And.is_logical_operator() is true
   - Expected: contracts.ContractExprKind.Ge.is_comparison() is true
   - Expected: contracts.ContractExprKind.Neg.is_arithmetic() is true
   - Expected: contracts.ContractExprKind.Len.is_unary_op() is true
   - Expected: contracts.ContractExprKind.Call.is_variable_reference() is false
   - Expected: contracts.ContractExprKind.Len.to_string() equals `len`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FV-UNIFIED-ATTRS
step("classify contract operators and render summaries")
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

- build a function contract and inspect its parts
   - Expected: contract.has_preconditions() is true
   - Expected: contract.has_postconditions() is true
   - Expected: contract.has_invariants() is true
   - Expected: contract.is_total() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FV-UNIFIED-ATTRS
step("build a function contract and inspect its parts")
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

- attempt an impure call in a contract and confirm rejection
   - Expected: errors.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FV-UNIFIED-ATTRS
step("attempt an impure call in a contract and confirm rejection")
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
# oracle: exactly one validation error per impure call
expect(errors.len()).to_equal(1)
expect(errors[0]).to_contain("pure expression")
```

</details>

#### Class invariants

#### can be marked public

- mark a contract public and confirm the flag
   - Expected: public_inv.class_name equals `Counter`
   - Expected: public_inv.is_public is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FV-UNIFIED-ATTRS
step("mark a contract public and confirm the flag")
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

- render invariant and theorem scaffolding


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-FV-UNIFIED-ATTRS
step("render invariant and theorem scaffolding")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Unified Verification Attributes.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-FV-UNIFIED-ATTRS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2f838b6a835d2755472c104ec294ad8a52d43dec0ab8f39f8fb34f3d21427a08`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f838b6a835d2755472c104ec294ad8a52d43dec0ab8f39f8fb34f3d21427a08`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f838b6a835d2755472c104ec294ad8a52d43dec0ab8f39f8fb34f3d21427a08`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/00_formal_verification/compiler/unified_attrs_spec.spl
mirror: doc/06_spec/00_formal_verification/compiler/unified_attrs_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/00_formal_verification/compiler/unified_attrs_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/00_formal_verification/compiler/unified_attrs_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/00_formal_verification/compiler/unified_attrs_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/00_formal_verification/compiler/unified_attrs_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/00_formal_verification/compiler/unified_attrs_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies operators and renders summaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/00_formal_verification/compiler/unified_attrs_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks requires, ensures, invariants, and termination' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/00_formal_verification/compiler/unified_attrs_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects impure calls in contracts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/00_formal_verification/compiler/unified_attrs_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be marked public' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
