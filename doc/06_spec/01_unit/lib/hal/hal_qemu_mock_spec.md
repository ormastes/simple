# QEMU Mock HAL Backend Specification

> Validates the QEMU mock HAL backend that provides an in-memory register map for testing typed MMIO register read/write operations without real hardware.

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
| Updated | 2026-08-26 |
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

- AC-6: creates mock with empty register map
   - Expected: reg_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: creates mock with empty register map")
val mock = qemu_mock_hal_new()

val reg_count = mock.registers.len()
expect(reg_count).to_equal(0)
```

</details>

### qemu_mock_write and qemu_mock_read

#### AC-6: write then read returns the written value

- AC-6: write then read returns the written value
   - Expected: value equals `0x12345678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: write then read returns the written value")
val mock = qemu_mock_hal_new()
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width32)

val mock2 = qemu_mock_write(mock, addr, 0x12345678)
val value = qemu_mock_read(mock2, addr)

expect(value).to_equal(0x12345678)
```

</details>

#### AC-6: reading an unwritten address returns 0

- AC-6: reading an unwritten address returns 0
   - Expected: value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: reading an unwritten address returns 0")
val mock = qemu_mock_hal_new()
val addr = mmio_address(0x40000000, 0x00, RegisterWidth.Width32)

val value = qemu_mock_read(mock, addr)
expect(value).to_equal(0)
```

</details>

#### AC-6: overwriting a register updates the value

- AC-6: overwriting a register updates the value
   - Expected: value equals `0xBBBB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: overwriting a register updates the value")
val mock = qemu_mock_hal_new()
val addr = mmio_address(0x40000000, 0x04, RegisterWidth.Width32)

val mock2 = qemu_mock_write(mock, addr, 0xAAAA)
val mock3 = qemu_mock_write(mock2, addr, 0xBBBB)
val value = qemu_mock_read(mock3, addr)

expect(value).to_equal(0xBBBB)
```

</details>

#### AC-6: different addresses store different values

- AC-6: different addresses store different values
   - Expected: val1 equals `0x1111`
   - Expected: val2 equals `0x2222`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: different addresses store different values")
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

- AC-6: irq is not pending initially
   - Expected: pending is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: irq is not pending initially")
val mock = qemu_mock_hal_new()
val line = irq_line(10)

val pending = qemu_mock_irq_pending(mock, line)
expect(pending).to_equal(false)
```

</details>

#### AC-6: inject_irq makes irq pending

- AC-6: inject_irq makes irq pending
   - Expected: pending is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: inject_irq makes irq pending")
val mock = qemu_mock_hal_new()
val line = irq_line(10)

val mock2 = qemu_mock_inject_irq(mock, line)
val pending = qemu_mock_irq_pending(mock2, line)

expect(pending).to_equal(true)
```

</details>

#### AC-6: different irq lines are independent

- AC-6: different irq lines are independent
   - Expected: pending10 is true
   - Expected: pending20 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: different irq lines are independent")
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

- AC-6: full round-trip: construct addr, write, read, verify
   - Expected: status equals `0x60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("AC-6: full round-trip: construct addr, write, read, verify")
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

- **Plan:** `doc/03_plan/pure_simple_lib_standalone_hw_plan.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0ced5ab1c10010cb991821cf8655d841d3f5f444365faeef7ffca84800abaa4b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ced5ab1c10010cb991821cf8655d841d3f5f444365faeef7ffca84800abaa4b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ced5ab1c10010cb991821cf8655d841d3f5f444365faeef7ffca84800abaa4b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/hal/hal_qemu_mock_spec.spl
mirror: doc/06_spec/01_unit/lib/hal/hal_qemu_mock_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/hal/hal_qemu_mock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/hal/hal_qemu_mock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/hal/hal_qemu_mock_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/hal/hal_qemu_mock_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: creates mock with empty register map' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hal/hal_qemu_mock_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: write then read returns the written value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/hal/hal_qemu_mock_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-6: reading an unwritten address returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
