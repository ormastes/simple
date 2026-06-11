# QEMU Mock HAL Backend Specification

> Validates the QEMU mock HAL backend that provides an in-memory register map for testing typed MMIO register read/write operations without real hardware.

<!-- sdn-diagram:id=hal_qemu_mock_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hal_qemu_mock_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hal_qemu_mock_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hal_qemu_mock_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU Mock HAL Backend Specification

Validates the QEMU mock HAL backend that provides an in-memory register map for testing typed MMIO register read/write operations without real hardware.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #hw-access-optimization-infra |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Plan | doc/03_plan/pure_simple_lib_standalone_hw_plan.md |
| Source | `test/01_unit/lib/hal/hal_qemu_mock_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the QEMU mock HAL backend that provides an in-memory register map
for testing typed MMIO register read/write operations without real hardware.

## Behavior

- QemuMockHal holds an in-memory register map (list of addr/value pairs)
- Mock read returns the stored value for a given MmioAddress
- Mock write updates the register map and returns new state
- Mock supports IRQ injection and pending queries
- All operations are pure (no side effects, returns new state)

## Scenarios

### QemuMockHal

### qemu_mock_hal_new

#### AC-6: creates mock with empty register map

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()

val reg_count = mock.registers.len()
expect(reg_count).to_equal(0)
```

</details>

### qemu_mock_write and qemu_mock_read

#### AC-6: write then read returns the written value

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width32)

val mock2 = qemu_mock_write(mock, addr, 0x12345678)
val value = qemu_mock_read(mock2, addr)

expect(value).to_equal(0x12345678)
```

</details>

#### AC-6: reading an unwritten address returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width32)

val value = qemu_mock_read(mock, addr)
expect(value).to_equal(0)
```

</details>

#### AC-6: overwriting a register updates the value

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()
val addr = mmio_address(0x40000000, 0x04, RegisterWidth.Width32)

val mock2 = qemu_mock_write(mock, addr, 0xAAAA)
val mock3 = qemu_mock_write(mock2, addr, 0xBBBB)
val value = qemu_mock_read(mock3, addr)

expect(value).to_equal(0xBBBB)
```

</details>

#### AC-6: different addresses store different values

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()
val addr1 = mmio_address(0x40000000, 0x00, RegisterWidth.Width32)
val addr2 = mmio_address(0x40000000, 0x04, RegisterWidth.Width32)

val mock2 = qemu_mock_write(mock, addr1, 0x1111)
val mock3 = qemu_mock_write(mock2, addr2, 0x2222)

val val1 = qemu_mock_read(mock3, addr1)
val val2 = qemu_mock_read(mock3, addr2)

expect(val1).to_equal(0x1111)
expect(val2).to_equal(0x2222)
```

</details>

### qemu_mock_irq

#### AC-6: irq is not pending initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()
val line = irq_line(10)

val pending = qemu_mock_irq_pending(mock, line)
expect(pending).to_equal(false)
```

</details>

#### AC-6: inject_irq makes irq pending

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()
val line = irq_line(10)

val mock2 = qemu_mock_inject_irq(mock, line)
val pending = qemu_mock_irq_pending(mock2, line)

expect(pending).to_equal(true)
```

</details>

#### AC-6: different irq lines are independent

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mock = qemu_mock_hal_new()
val line10 = irq_line(10)
val line20 = irq_line(20)

val mock2 = qemu_mock_inject_irq(mock, line10)

val pending10 = qemu_mock_irq_pending(mock2, line10)
val pending20 = qemu_mock_irq_pending(mock2, line20)

expect(pending10).to_equal(true)
expect(pending20).to_equal(false)
```

</details>

### typed MMIO round-trip

#### AC-6: full round-trip: construct addr, write, read, verify

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange: create mock and typed MMIO address for a UART status register
val mock = qemu_mock_hal_new()
val uart_status_addr = mmio_address(0x10000000, 0x14, RegisterWidth.Width32)

# Act: write a status value and read it back
val mock2 = qemu_mock_write(mock, uart_status_addr, 0x60)
val status = qemu_mock_read(mock2, uart_status_addr)

# Assert: THRE + TEMT bits (0x60) should be set
expect(status).to_equal(0x60)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/pure_simple_lib_standalone_hw_plan.md](doc/03_plan/pure_simple_lib_standalone_hw_plan.md)


</details>
