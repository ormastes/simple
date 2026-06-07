# Native Bridge Specification

> <details>

<!-- sdn-diagram:id=native_bridge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_bridge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_bridge_spec -> std
native_bridge_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_bridge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Bridge Specification

## Scenarios

### Native Bridge

#### builds compile result values for success and failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val success = nativecompileresult_success_result("/tmp/native-bin", 123)
val failure = nativecompileresult_error_result("linker failed")

expect(success.success).to_equal(true)
expect(success.binary_path).to_equal("/tmp/native-bin")
expect(success.error_message).to_equal("")
expect(success.compile_time_ms).to_equal(123)

expect(failure.success).to_equal(false)
expect(failure.binary_path).to_equal("")
expect(failure.error_message).to_equal("linker failed")
expect(failure.compile_time_ms).to_equal(0)
```

</details>

#### preserves execution result fields on hand-built values

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = NativeExecutionResult(
    stdout: "stdout text",
    stderr: "stderr text",
    exit_code: 7,
    execution_time_ms: 42
)

expect(result.stdout).to_equal("stdout text")
expect(result.stderr).to_equal("stderr text")
expect(result.exit_code).to_equal(7)
expect(result.execution_time_ms).to_equal(42)
```

</details>

#### returns a boolean-shaped native availability value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = is_native_available()

expect(available == true or available == false).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_bridge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
