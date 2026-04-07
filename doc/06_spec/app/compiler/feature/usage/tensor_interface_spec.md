# Tensor Interface Consistency Specification

Tests that tensor interfaces are consistent between core and torch.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1920, #1930 |
| Category | ML, Collections, API |
| Status | Complete |
| Source | `test/feature/usage/tensor_interface_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

Tests that tensor interfaces are consistent between core and torch.
Verifies that basic tensor operations work the same way regardless
of the underlying implementation.

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `target/test-artifacts/feature/usage/tensor_interface/result.json` |

## Scenarios

- creates tensor from array
- creates tensor with explicit shape
- creates zero tensor
- creates ones tensor
- accesses elements by index
- supports negative indexing
- slices tensors
- performs element-wise addition
- performs element-wise multiplication
- performs matrix multiplication with @
- gets tensor shape
- gets tensor dimension count
- gets tensor element count
- gets tensor dtype
- gets tensor device
- reshapes tensor
- flattens tensor
- transposes 2D tensor
- creates tensor with device config
- creates tensor metadata dict
- stores tensor info in dict
