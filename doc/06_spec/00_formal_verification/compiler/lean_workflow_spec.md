# Lean Workflow Specification

> 1. exit code: Some

<!-- sdn-diagram:id=lean_workflow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lean_workflow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lean_workflow_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lean_workflow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Workflow Specification

## Scenarios

### Lean Verification Workflow Core

#### LeanCheckResult

#### flags unproven goals and formats them

1. exit code: Some
   - Expected: result.has_unproven() is true
   - Expected: result.is_fully_proven() is false
   - Expected: result.passed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = runner.LeanCheckResult(
    file: "src/verification/demo.lean",
    success: true,
    stdout: "goals accomplished",
    stderr: "",
    goals_solved: 1,
    goals_remaining: 2,
    exit_code: Some(0)
)

expect(result.has_unproven()).to_equal(true)
expect(result.is_fully_proven()).to_equal(false)
expect(result.passed()).to_equal(true)
expect(result.format()).to_contain("Goals remaining (sorry): 2")
```

</details>

#### VerificationSummary

#### aggregates pass/fail and unproven counts

1. exit code: Some
2. exit code: Some
   - Expected: summary.files_checked equals `2`
   - Expected: summary.files_passed equals `1`
   - Expected: summary.files_failed equals `1`
   - Expected: summary.total_theorems equals `2`
   - Expected: summary.proven_theorems equals `1`
   - Expected: summary.unproven_theorems equals `1`
   - Expected: summary.is_success() is false
   - Expected: summary.is_fully_proven() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = runner.LeanCheckResult(
    file: "src/verification/ok.lean",
    success: true,
    stdout: "goals accomplished",
    stderr: "",
    goals_solved: 1,
    goals_remaining: 0,
    exit_code: Some(0)
)
val bad = runner.LeanCheckResult(
    file: "src/verification/bad.lean",
    success: false,
    stdout: "",
    stderr: "error: sorry",
    goals_solved: 0,
    goals_remaining: 1,
    exit_code: Some(1)
)

val summary = runner.VerificationSummary.from_results([ok, bad])
expect(summary.files_checked).to_equal(2)
expect(summary.files_passed).to_equal(1)
expect(summary.files_failed).to_equal(1)
expect(summary.total_theorems).to_equal(2)
expect(summary.proven_theorems).to_equal(1)
expect(summary.unproven_theorems).to_equal(1)
expect(summary.is_success()).to_equal(false)
expect(summary.is_fully_proven()).to_equal(false)
expect(summary.format()).to_contain("Files: 1/2 passed")
expect(summary.format()).to_contain("Theorems: 1/2 proven")
expect(summary.format()).to_contain("Unproven (sorry): 1")
```

</details>

#### Proof obligations

#### extracts obligations with stable identifiers

1. var contract = contracts FunctionContract new
2. contracts ContractExpr variable
3. contracts ContractExpr int val
4. contracts ContractExpr result
5. contracts ContractExpr int val
6. contracts ContractExpr variable
7. contracts ContractExpr int val
   - Expected: obls.len() equals `3`
   - Expected: obls[0].id equals `factorial_pre_0`
   - Expected: obls[1].id equals `factorial_post_0`
   - Expected: obls[2].id equals `factorial_inv_0`
   - Expected: obls[0].source_file equals `math.spl`
   - Expected: obls[0].source_line equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
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

val obls = obligations.extract_from_contract("factorial", "math.spl", 42, contract)
expect(obls.len()).to_equal(3)
expect(obls[0].id).to_equal("factorial_pre_0")
expect(obls[1].id).to_equal("factorial_post_0")
expect(obls[2].id).to_equal("factorial_inv_0")
expect(obls[0].source_file).to_equal("math.spl")
expect(obls[0].source_line).to_equal(42)
```

</details>

#### preserves proof text when marked proven

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ob = obligations.ProofObligation.create(
    "demo_post_0",
    "demo_postcondition_0",
    "demo.spl",
    7,
    "True"
)
val proven = ob.with_status(obligations.ProofStatus.Proven).with_proof("rfl")
val theorem = proven.to_lean_theorem()

expect(proven.status.to_string()).to_equal("proven")
expect(theorem.name).to_equal("demo_postcondition_0")
expect(theorem.proof).to_equal("rfl")
expect(theorem.to_lean()).to_contain("rfl")
```

</details>

#### Regeneration inventory

#### returns the supported file set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = regen.regenerate_all()
expect(files.len()).to_equal(15)
expect(files.has("src/verification/memory_capabilities/src/MemoryCapabilities.lean")).to_equal(true)
expect(files.has("src/verification/memory_model_drf/src/MemoryModelDRF.lean")).to_equal(true)
expect(files.has("src/verification/type_inference_compile/src/Contracts.lean")).to_equal(true)
```

</details>

#### writes regenerated files to a temp directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_root = "/tmp/simple-lean-workflow-unit"
val sample = {"src/verification/demo/src/Demo.lean": "theorem demo : True := by rfl"}
val written = regen.write_regenerated_files(sample, temp_root)

expect(written.len()).to_equal(1)
expect(written[0]).to_start_with(temp_root)
expect(fs.exist(written[0])).to_equal(true)
expect(fs.read_text(written[0])).to_equal("theorem demo : True := by rfl")
```

</details>

#### Proof status

#### renders admitted and pending states distinctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(obligations.ProofStatus.Pending.to_string()).to_equal("pending")
expect(obligations.ProofStatus.Proven.to_string()).to_equal("proven")
expect(obligations.ProofStatus.Admitted.to_string()).to_equal("admitted")
```

</details>

#### Strict checker

#### hard-fails on files that still contain sorry

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val temp_root = "/tmp/simple-lean-workflow-strict"
val temp_path = "{temp_root}/Demo.lean"
val written = regen.write_regenerated_files(
    {"src/verification/demo/src/Demo.lean": "theorem demo : True := by sorry"},
    temp_root
)

expect(written.len()).to_equal(1)

val proof_checker = checker.ProofChecker.create()
val result = proof_checker.check_file(temp_path)

expect(result.status).to_equal(checker.ProofStatus.Failed)
expect(result.sorry_count).to_equal(1)
expect(result.error_message).to_contain("sorry")
```

</details>

#### flags missing validation targets as mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validation = regen.validate_regeneration(
    {"src/verification/demo/src/Demo.lean": "theorem demo : True := by rfl"},
    "/tmp/simple-lean-workflow-missing"
)

expect(validation.has("src/verification/demo/src/Demo.lean")).to_equal(true)
expect(validation.get("src/verification/demo/src/Demo.lean").?).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/lean_workflow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Verification Workflow Core

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
