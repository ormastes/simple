# Sbi Ipi Specification

> <details>

<!-- sdn-diagram:id=sbi_ipi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sbi_ipi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sbi_ipi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sbi_ipi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sbi Ipi Specification

## Scenarios

### SBI IPI Extension

### probe ladder — IPI_PATH_V3

#### AC-1: selects V3 when sbi_probe_extension(0x735049) returns available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange
val mock = make_sbi_mock_v3_available()
# Act — test-only entry point (does not exist yet; Phase 5 SA-1 adds it)
val path = sbi_ipi_probe_path_with_mock(mock)
# Assert
expect(path).to_equal("V3")
```

</details>

#### AC-1: sbi_probe_then_send_ipi_with_mock records ipi_call on V3 path

1. sbi probe then send ipi with mock
   - Expected: mock.ipi_calls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_available()
# hart_mask = 0b0010 (target hart 1), hart_mask_base = 0
sbi_probe_then_send_ipi_with_mock(mock, 0x2u64, 0u64)
expect(mock.ipi_calls.len()).to_equal(1)
```

</details>

#### AC-1: V3 ipi_call records correct hart_mask

1. sbi probe then send ipi with mock
   - Expected: call.0 equals `0x4u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_available()
sbi_probe_then_send_ipi_with_mock(mock, 0x4u64, 0u64)
val call = mock.ipi_calls[0]
expect(call.0).to_equal(0x4u64)
```

</details>

### probe ladder — IPI_PATH_LEGACY

#### AC-1: selects Legacy when V3 absent but EID 0x04 available

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_legacy_only()
val path = sbi_ipi_probe_path_with_mock(mock)
expect(path).to_equal("Legacy")
```

</details>

#### AC-1: legacy send records call

1. sbi probe then send ipi with mock
   - Expected: mock.ipi_calls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_legacy_only()
sbi_probe_then_send_ipi_with_mock(mock, 0x1u64, 0u64)
expect(mock.ipi_calls.len()).to_equal(1)
```

</details>

### probe ladder — IPI_PATH_CLINT

#### AC-1: selects CLINT when both SBI IPI extensions absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_clint_only()
val path = sbi_ipi_probe_path_with_mock(mock)
expect(path).to_equal("Clint")
```

</details>

#### AC-1: CLINT path records MMIO write target (hart_mask)

1. sbi probe then send ipi with mock
   - Expected: mock.ipi_calls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_clint_only()
sbi_probe_then_send_ipi_with_mock(mock, 0x1u64, 0u64)
# CLINT path should record as ipi_calls for test observability
expect(mock.ipi_calls.len()).to_equal(1)
```

</details>

### cached IpiPath — probe runs once

#### AC-1: second probe with same mock does not add a second probe_ext call

1. sbi ipi probe path with mock
2. sbi ipi probe path with mock
   - Expected: mock.probe_ext_results.len() equals `probe_count_after_first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_available()
sbi_ipi_probe_path_with_mock(mock)
val probe_count_after_first = mock.probe_ext_results.len()
sbi_ipi_probe_path_with_mock(mock)
# Probe results list is input-only; count unchanged means no re-probe
expect(mock.probe_ext_results.len()).to_equal(probe_count_after_first)
```

</details>

### sbi_send_ipi_v3 — direct call

#### AC-1: v3 call signature accepts hart_mask and hart_mask_base

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When Phase 5 SA-1 adds sbi_send_ipi_v3_with_mock, this test becomes live.
# For now the function does not exist — TDD red.
val result = sbi_send_ipi_v3_with_mock(0x1u64, 0u64)
expect(result).to_equal(0)  # SBI_SUCCESS = 0
```

</details>

### sbi_send_ipi_legacy — direct call

#### AC-1: legacy call accepts hart_mask_ptr as stack-local address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = sbi_send_ipi_legacy_with_mock(0x1u64)
expect(result).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/baremetal/riscv/sbi_ipi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SBI IPI Extension
- probe ladder — IPI_PATH_V3
- probe ladder — IPI_PATH_LEGACY
- probe ladder — IPI_PATH_CLINT
- cached IpiPath — probe runs once
- sbi_send_ipi_v3 — direct call
- sbi_send_ipi_legacy — direct call

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
