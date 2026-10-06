# Lean Verification Workflow Specification

> Tests covering Lean Verification Workflow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Verification Workflow Specification

## Scenarios

### Lean Verification Workflow

#### Code generation

#### assembles Lean codegen state

- assembles Lean codegen state
   - Expected: gen.options.module_name equals `SystemDemo`
   - Expected: gen.options.output_dir equals `temp_root`
   - Expected: gen.functions.len() equals `1`
   - Expected: gen.theorems.len() equals `1`
   - Expected: gen.functions[0].name equals `system_demo`
   - Expected: gen.theorems[0].name equals `system_demo_nonnegative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assembles Lean codegen state")
val temp_root = "/tmp/simple-lean-verification-system"

var opts = codegen.LeanCodegenOptions.new()
opts = opts.with_module_name("SystemDemo")
opts = opts.with_output_dir(temp_root)
opts = opts.with_stubs(false)

var gen = codegen.LeanCodegen.new(opts)

var func = codegen.LeanFunction.new("system_demo")
func = func.add_param("x", "Int")
func = func.with_return_type("Int")
func = func.with_body("x")
gen = gen.add_function(func)

var thm = codegen.LeanTheorem.new("system_demo_nonnegative", "system_demo x >= 0")
thm = thm.add_param("x", "Int")
gen = gen.add_theorem(thm)

expect(gen.options.module_name).to_equal("SystemDemo")
expect(gen.options.output_dir).to_equal(temp_root)
expect(gen.functions.len()).to_equal(1)
expect(gen.theorems.len()).to_equal(1)
expect(gen.functions[0].name).to_equal("system_demo")
expect(gen.theorems[0].name).to_equal("system_demo_nonnegative")
```

</details>

#### Summary reporting

#### formats a mixed proof summary

- formats a mixed proof summary
   - Expected: summary.files_checked equals `2`
   - Expected: summary.files_passed equals `2`
   - Expected: summary.files_failed equals `0`
   - Expected: summary.total_theorems equals `3`
   - Expected: summary.proven_theorems equals `1`
   - Expected: summary.unproven_theorems equals `2`
   - Expected: summary.is_success() is true
   - Expected: summary.is_fully_proven() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats a mixed proof summary")
val proven = runner.LeanCheckResult(
    file: "src/verification/proven.lean",
    success: true,
    stdout: "goals accomplished",
    stderr: "",
    goals_solved: 1,
    goals_remaining: 0,
    exit_code: Some(0)
)
val pending = runner.LeanCheckResult(
    file: "src/verification/pending.lean",
    success: true,
    stdout: "sorry",
    stderr: "",
    goals_solved: 0,
    goals_remaining: 2,
    exit_code: Some(0)
)

val summary = runner.VerificationSummary.from_results([proven, pending])
expect(summary.files_checked).to_equal(2)
expect(summary.files_passed).to_equal(2)
expect(summary.files_failed).to_equal(0)
expect(summary.total_theorems).to_equal(3)
expect(summary.proven_theorems).to_equal(1)
expect(summary.unproven_theorems).to_equal(2)
expect(summary.is_success()).to_equal(true)
expect(summary.is_fully_proven()).to_equal(false)
expect(summary.format()).to_contain("Files: 2/2 passed")
expect(summary.format()).to_contain("Theorems: 1/3 proven")
expect(summary.format()).to_contain("Admitted (sorry): 2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/lean_verification_workflow_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean Verification Workflow.
- Lean Verification Workflow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
