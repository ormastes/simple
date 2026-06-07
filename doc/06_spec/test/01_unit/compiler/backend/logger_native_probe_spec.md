# Logger Native Probe Specification

> 1. rt file delete

<!-- sdn-diagram:id=logger_native_probe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=logger_native_probe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

logger_native_probe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=logger_native_probe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Logger Native Probe Specification

## Scenarios

### logger native probe

#### gates simple_log_c_write output behind log_set_targets on hosted fallback

1. rt file delete
2. rt file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_path = "/tmp/simple_logger_native_probe.spl"
val binary_path = "/tmp/simple_logger_native_probe"
expect(rt_file_write_text(source_path, _probe_source())).to_equal(true)

val compile_result = rt_compile_to_native(source_path, binary_path)
expect(compile_result[0]).to_equal(true)

val exec_result = rt_execute_native(binary_path, [], 5000)
val stdout = exec_result[0]
val exit_code = exec_result[2]

expect(exit_code).to_equal(0)
expect(stdout).to_contain("keep-me")
expect(stdout.contains("drop-me")).to_equal(false)

rt_file_delete(source_path)
rt_file_delete(binary_path)
```

</details>

#### does not borrow repo context for ordinary external paths

1. rt file delete
2. rt file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source_path = "../simple_logger_native_probe_outside.spl"
val binary_path = "../simple_logger_native_probe_outside"
expect(rt_file_write_text(source_path, _probe_source())).to_equal(true)

val compile_result = rt_compile_to_native(source_path, binary_path)
expect(compile_result[0]).to_equal(false)
expect(compile_result[1] == "").to_equal(false)

rt_file_delete(source_path)
rt_file_delete(binary_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/logger_native_probe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- logger native probe

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
