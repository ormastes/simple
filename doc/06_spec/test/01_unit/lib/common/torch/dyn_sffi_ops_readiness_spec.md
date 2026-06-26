# Dyn Sffi Ops Readiness Specification

> <details>

<!-- sdn-diagram:id=dyn_sffi_ops_readiness_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dyn_sffi_ops_readiness_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dyn_sffi_ops_readiness_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dyn_sffi_ops_readiness_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dyn Sffi Ops Readiness Specification

## Scenarios

### dynamic torch SFFI readiness surface

#### delegates availability to the runtime facade instead of hardcoding false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = dyn_available_body(source_text())

expect(body).to_contain("fn dyn_torch_available() -> bool:")
expect(body).to_contain("rt_torch_available()")
expect(body.contains("\n    false")).to_equal(false)
expect(body.contains("return false")).to_equal(false)
```

</details>

#### delegates linalg solve to the existing runtime SFFI instead of hardcoding failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = source_text()
val body = dyn_linalg_solve_body(source)

expect(body).to_contain("fn dyn_torch_tensor_linalg_solve(a: i64, b: i64) -> i64:")
expect(body).to_contain("if not rt_torch_available():")
expect(body).to_contain("return 0")
expect(body).to_contain("rt_torch_torchtensor_linalg_solve(a, b)")
expect(body.contains("not yet implemented")).to_equal(false)
expect(source).to_contain("extern fn rt_torch_torchtensor_linalg_solve(a: i64, b: i64) -> i64")

val runtime = rust_linalg_runtime_source()
expect(runtime).to_contain("pub extern \"C\" fn rt_torch_linalg_solve")
expect(runtime).to_contain("pub extern \"C\" fn rt_torch_torchtensor_linalg_solve")
expect(runtime).to_contain("rt_torch_linalg_solve(a_handle, b_handle)")
```

</details>

#### keeps linalg solve safe for invalid runtime handles

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(dyn_torch_tensor_linalg_solve(0, 0)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/torch/dyn_sffi_ops_readiness_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- dynamic torch SFFI readiness surface

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
