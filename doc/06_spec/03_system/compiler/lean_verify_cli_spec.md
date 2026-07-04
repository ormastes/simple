# Lean Verify Cli Specification

> <details>

<!-- sdn-diagram:id=lean_verify_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lean_verify_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lean_verify_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lean_verify_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean Verify Cli Specification

## Scenarios

### Lean verification CLI

#### simple verify status

#### reports the shared Lean verification inventory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple = simple_binary()
val result = shell(simple + " verify status")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("Verification Status")
expect(result.stdout).to_contain("Lean 4:")
expect(result.stdout).to_contain("src/verification/nogc_compile/src/NogcCompile.lean")
expect(result.stdout).to_contain("src/verification/type_inference_compile/src/Generics.lean")
expect(result.stdout).to_contain("src/verification/tensor_dimensions/src/TensorMemory.lean")
expect(result.stderr).to_equal("")
```

</details>

#### simple verify list

#### lists the authoritative verification files

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple = simple_binary()
val result = shell(simple + " verify list")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("Verification Artifact Inventory")
expect(result.stdout).to_contain("src/verification/nogc_compile/src/NogcCompile.lean")
expect(result.stdout).to_contain("src/verification/memory_model_drf/src/MemoryModelDRF.lean")
expect(result.stderr).to_equal("")
```

</details>

#### simple verify check

#### passes against the generated verification tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple = simple_binary()
val result = shell(simple + " verify check")
expect(result.exit_code).to_equal(0)
expect(result.stdout).to_contain("Verification Summary:")
expect(result.stdout).to_contain("Files: 15/15 passed")
expect(result.stdout).to_contain("src/verification/memory_model_drf/src/MemoryModelDRF.lean")
expect(result.stderr).to_equal("")
```

</details>

#### gen-lean compatibility

#### regenerates a project and keeps verification green

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple = simple_binary()
val write_result = shell(simple + " gen-lean write --force --project type_inference_compile")
expect(write_result.exit_code).to_equal(0)
expect((write_result.stdout + write_result.stderr)).to_contain("src/verification/type_inference_compile/src/Generics.lean")

val verify_result = shell(simple + " verify check")
expect(verify_result.exit_code).to_equal(0)
expect(verify_result.stdout).to_contain("Files: 15/15 passed")
expect(verify_result.stdout.contains("warning:")).to_equal(false)
expect(verify_result.stderr).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/lean_verify_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean verification CLI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
