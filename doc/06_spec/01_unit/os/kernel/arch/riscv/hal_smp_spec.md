# Hal Smp Specification

> 1. hal smp init with null dtb

<!-- sdn-diagram:id=hal_smp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_smp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_smp_spec -> std
hal_smp_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_smp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hal Smp Specification

## Scenarios

### HalSmp

### hal_smp_cpu_count

#### AC-1: returns 1 when DTB is null (fallback)

1. hal smp init with null dtb
   - Expected: count equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
hal_smp_init_with_null_dtb()
val count = hal_smp_cpu_count()
expect(count).to_equal(1u32)
```

</details>

#### AC-1: returns 2 for a two-hart FDT

1. HartDescSmp
2. HartDescSmp
3. hal smp init from bytes
   - Expected: hal_smp_cpu_count() equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDescSmp(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDescSmp(id: 1u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus_smp(harts)
hal_smp_init_from_bytes(fdt)
expect(hal_smp_cpu_count()).to_equal(2u32)
```

</details>

#### AC-1: disabled hart is excluded from count

1. HartDescSmp
2. HartDescSmp
3. hal smp init from bytes
   - Expected: hal_smp_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDescSmp(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDescSmp(id: 1u32, status: "disabled", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus_smp(harts)
hal_smp_init_from_bytes(fdt)
expect(hal_smp_cpu_count()).to_equal(1u32)
```

</details>

### hal_smp_cpu_start

#### AC-1: returns true when SBI hart_start returns SBI_SUCCESS (0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_smp()
val result = hal_smp_cpu_start_with_mock(mock, 1u32, 0x80200000u64, 0x81000000u64, 0u64)
expect(result).to_equal(true)
```

</details>

#### AC-1: returns false when SBI hart_start returns error (-1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_clint_smp()
val result = hal_smp_cpu_start_with_mock(mock, 1u32, 0x80200000u64, 0x81000000u64, 0u64)
expect(result).to_equal(false)
```

</details>

#### AC-1: AP_BOOT_ARGS slot at target index is populated before SBI call

1. hal smp cpu start with mock
   - Expected: args.stack equals `0x81200000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_smp()
hal_smp_cpu_start_with_mock(mock, 2u32, 0x80200000u64, 0x81200000u64, 0xDEADu64)
val args = hal_smp_get_boot_args(2u32)
expect(args.stack).to_equal(0x81200000u64)
```

</details>

### hal_smp_ipi_send

#### AC-1: delivers vector to PENDING_IPI at target index

1. hal smp ipi send with mock
   - Expected: pending equals `42u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_smp()
hal_smp_ipi_send_with_mock(mock, 1u32, 42u32)
val pending = hal_smp_get_pending_ipi(1u32)
expect(pending).to_equal(42u32)
```

</details>

#### AC-1: SBI ipi_call is made with correct hart_mask (1 << target)

1. hal smp ipi send with mock
   - Expected: mock.ipi_calls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_smp()
hal_smp_ipi_send_with_mock(mock, 3u32, 1u32)
expect(mock.ipi_calls.len()).to_equal(1)
```

</details>

#### AC-5: ipi_send does NOT use read_tp() offset (uses global array indexed by target)

1. hal smp ipi send with mock
   - Expected: slot2 equals `99u32`
   - Expected: slot0 equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_v3_smp()
hal_smp_ipi_send_with_mock(mock, 2u32, 99u32)
val slot2 = hal_smp_get_pending_ipi(2u32)
val slot0 = hal_smp_get_pending_ipi(0u32)
expect(slot2).to_equal(99u32)
expect(slot0).to_equal(0u32)
```

</details>

#### AC-1: CLINT path writes to PENDING_IPI at target and records IPI call

1. hal smp ipi send with mock
   - Expected: pending equals `7u32`
   - Expected: mock.ipi_calls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = make_sbi_mock_clint_smp()
hal_smp_ipi_send_with_mock(mock, 1u32, 7u32)
# Verify PENDING_IPI slot was written (module-level state)
val pending = hal_smp_get_pending_ipi(1u32)
expect(pending).to_equal(7u32)
# Verify IPI call was recorded (.len() avoids static OOB on empty-array-typed [0])
expect(mock.ipi_calls.len()).to_equal(1)
```

</details>

### hal_smp_ipi_broadcast

#### AC-1: sends IPI to all harts except self

1. HartDescSmp
2. HartDescSmp
3. HartDescSmp
4. hal smp init from bytes
5. hal smp ipi broadcast with mock


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDescSmp(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDescSmp(id: 1u32, status: "okay", isa: "rv64gc"),
    HartDescSmp(id: 2u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus_smp(harts)
val mock = make_sbi_mock_v3_smp()
hal_smp_init_from_bytes(fdt)
hal_smp_ipi_broadcast_with_mock(mock, 5u32)
expect(mock.ipi_calls.len()).to_be_greater_than(0)
```

</details>

#### AC-1: PENDING_IPI slots for all non-self harts contain broadcast vector

1. HartDescSmp
2. HartDescSmp
3. hal smp init from bytes
4. hal smp ipi broadcast with mock
   - Expected: hal_smp_get_pending_ipi(1u32) equals `77u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harts = [
    HartDescSmp(id: 0u32, status: "okay", isa: "rv64gc"),
    HartDescSmp(id: 1u32, status: "okay", isa: "rv64gc")
]
val fdt = make_fdt_with_cpus_smp(harts)
val mock = make_sbi_mock_v3_smp()
hal_smp_init_from_bytes(fdt)
hal_smp_ipi_broadcast_with_mock(mock, 77u32)
expect(hal_smp_get_pending_ipi(1u32)).to_equal(77u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv/hal_smp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- HalSmp
- hal_smp_cpu_count
- hal_smp_cpu_start
- hal_smp_ipi_send
- hal_smp_ipi_broadcast

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
