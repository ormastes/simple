# Host Gpu Lane Codegen Marker Specification

> <details>

<!-- sdn-diagram:id=host_gpu_lane_codegen_marker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_gpu_lane_codegen_marker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_gpu_lane_codegen_marker_spec -> std
host_gpu_lane_codegen_marker_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_gpu_lane_codegen_marker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Lane Codegen Marker Specification

## Scenarios

### Host/GPU lane native codegen markers

#### consumes lane markers as queue-boundary accounting instead of unsupported instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(marker_codegen_score()).to_equal(1111111)
```

</details>

#### diagnoses an unmatched host GPU lane end marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unmatched_end_error_count()).to_equal(1)
```

</details>

#### keeps Cranelift helper calls uniquely named for bootstrap dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = legacy_codegen_source()

expect(source).to_contain("self.compile_cranelift_terminator(block.terminator)")
expect(source).to_contain("val cl_value = self.compile_cranelift_const(value, type_)")
expect(source).to_contain("self.get_cranelift_local(local)")
expect(source).to_contain("self.compile_cranelift_binop(op, lv, rv)")
expect(source).to_contain("self.compile_cranelift_unaryop(op, v)")
expect(source).to_contain("codegen.compile_cranelift_function(fn_)")
expect(source).to_not_contain("self.compile_terminator(block.terminator)")
expect(source).to_not_contain("self.compile_const(value, type_)")
expect(source).to_not_contain("self.get_local(local)")
expect(source).to_not_contain("self.compile_binop(op, lv, rv)")
expect(source).to_not_contain("self.compile_unaryop(op, v)")
expect(source).to_not_contain("codegen.compile_function(fn_)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/host_gpu_lane_codegen_marker_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Host/GPU lane native codegen markers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
