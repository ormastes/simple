# Tool Checker Specification

> <details>

<!-- sdn-diagram:id=tool_checker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tool_checker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tool_checker_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tool_checker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tool Checker Specification

## Scenarios

### Lean Verification Tool Checker

#### inventory

#### uses the authoritative Lean artifact list

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = checker.known_verification_files()

expect(files.len()).to_equal(15)
expect(files.contains("src/verification/nogc_compile/src/NogcCompile.lean")).to_equal(true)
expect(files.contains("src/verification/type_inference_compile/src/Contracts.lean")).to_equal(true)
expect(files.contains("src/verification/tensor_dimensions/src/TensorMemory.lean")).to_equal(true)
```

</details>

#### summary formatting

#### renders failed proof results with sorry details

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = checker.ProofResult(
    file_path: "src/verification/demo/src/Demo.lean",
    status: checker.ProofStatus.Failed,
    sorry_count: 2,
    error_message: "contains sorry",
    theorem_count: 3
)

expect(result.summary_line()).to_contain("[failed]")
expect(result.summary_line()).to_contain("3 theorems")
expect(result.summary_line()).to_contain("2 sorry")
expect(result.summary_line()).to_contain("contains sorry")
```

</details>

#### aggregates verification summary counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = checker.ProofResult(
    file_path: "src/verification/a.lean",
    status: checker.ProofStatus.Verified,
    sorry_count: 0,
    error_message: "",
    theorem_count: 2
)
val bad = checker.ProofResult(
    file_path: "src/verification/b.lean",
    status: checker.ProofStatus.Failed,
    sorry_count: 1,
    error_message: "contains sorry",
    theorem_count: 1
)

val summary = checker.CheckResult(file_results: [ok, bad]).summary()
expect(summary).to_contain("Files checked: 2")
expect(summary).to_contain("Verified:  1")
expect(summary).to_contain("Failed:    1")
expect(summary).to_contain("Theorems: 3")
expect(summary).to_contain("Pending proofs (sorry): 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/tool_checker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean Verification Tool Checker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
