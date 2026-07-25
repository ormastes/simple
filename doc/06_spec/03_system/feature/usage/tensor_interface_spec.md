# Tensor Interface Consistency Specification

> Tests that tensor interfaces are consistent between core and torch.

<!-- sdn-diagram:id=tensor_interface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_interface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_interface_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_interface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Interface Consistency Specification

Tests that tensor interfaces are consistent between core and torch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1920, #1930 |
| Category | ML, Collections, API |
| Status | Complete |
| Source | `test/03_system/feature/usage/tensor_interface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that tensor interfaces are consistent between core and torch.
Verifies that basic tensor operations work the same way regardless
of the underlying implementation.

## Scenarios

### Tensor Interface Consistency

#### env_skip: requires SIMPLE_GPU_TEST

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
