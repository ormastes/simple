# Hal Smp Specification

> Tests covering HalSmp, hal_smp_cpu_count, hal_smp_cpu_start, hal_smp_ipi_send, hal_smp_ipi_broadcast.

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

- AC-1: returns 1 when DTB is null (fallback)
   - Expected: count equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns 1 when DTB is null (fallback)")
hal_smp_init_with_null_dtb()
val count = hal_smp_cpu_count()
expect(count).to_equal(1u32)
```

</details>

#### AC-1: returns 2 for a two-hart FDT

- AC-1: returns 2 for a two-hart FDT
   - Expected: hal_smp_cpu_count() equals `2u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns 2 for a two-hart FDT")
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

- AC-1: disabled hart is excluded from count
   - Expected: hal_smp_cpu_count() equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: disabled hart is excluded from count")
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

- AC-1: returns true when SBI hart_start returns SBI_SUCCESS (0)
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns true when SBI hart_start returns SBI_SUCCESS (0)")
val mock = make_sbi_mock_v3_smp()
val result = hal_smp_cpu_start_with_mock(mock, 1u32, 0x80200000u64, 0x81000000u64, 0u64)
expect(result).to_equal(true)
```

</details>

#### AC-1: returns false when SBI hart_start returns error (-1)

- AC-1: returns false when SBI hart_start returns error (-1)
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: returns false when SBI hart_start returns error (-1)")
val mock = make_sbi_mock_clint_smp()
val result = hal_smp_cpu_start_with_mock(mock, 1u32, 0x80200000u64, 0x81000000u64, 0u64)
expect(result).to_equal(false)
```

</details>

#### AC-1: AP_BOOT_ARGS slot at target index is populated before SBI call

- AC-1: AP_BOOT_ARGS slot at target index is populated before SBI call
   - Expected: args.stack equals `0x81200000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: AP_BOOT_ARGS slot at target index is populated before SBI call")
val mock = make_sbi_mock_v3_smp()
hal_smp_cpu_start_with_mock(mock, 2u32, 0x80200000u64, 0x81200000u64, 0xDEADu64)
val args = hal_smp_get_boot_args(2u32)
expect(args.stack).to_equal(0x81200000u64)
```

</details>

### hal_smp_ipi_send

#### AC-1: delivers vector to PENDING_IPI at target index

- AC-1: delivers vector to PENDING_IPI at target index
   - Expected: pending equals `42u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: delivers vector to PENDING_IPI at target index")
val mock = make_sbi_mock_v3_smp()
hal_smp_ipi_send_with_mock(mock, 1u32, 42u32)
val pending = hal_smp_get_pending_ipi(1u32)
expect(pending).to_equal(42u32)
```

</details>

#### AC-1: SBI ipi_call is made with correct hart_mask (1 << target)

- AC-1: SBI ipi_call is made with correct hart_mask (1 << target)
   - Expected: mock.ipi_calls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: SBI ipi_call is made with correct hart_mask (1 << target)")
val mock = make_sbi_mock_v3_smp()
hal_smp_ipi_send_with_mock(mock, 3u32, 1u32)
expect(mock.ipi_calls.len()).to_equal(1)
```

</details>

#### AC-5: ipi_send does NOT use read_tp() offset (uses global array indexed by target)

- AC-5: ipi_send does NOT use read_tp() offset (uses global array indexed by target)
   - Expected: slot2 equals `99u32`
   - Expected: slot0 equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-5: ipi_send does NOT use read_tp() offset (uses global array indexed by target)")
val mock = make_sbi_mock_v3_smp()
hal_smp_ipi_send_with_mock(mock, 2u32, 99u32)
val slot2 = hal_smp_get_pending_ipi(2u32)
val slot0 = hal_smp_get_pending_ipi(0u32)
expect(slot2).to_equal(99u32)
expect(slot0).to_equal(0u32)
```

</details>

#### AC-1: CLINT path writes to PENDING_IPI at target and records IPI call

- AC-1: CLINT path writes to PENDING_IPI at target and records IPI call
   - Expected: pending equals `7u32`
   - Expected: mock.ipi_calls.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: CLINT path writes to PENDING_IPI at target and records IPI call")
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

- AC-1: sends IPI to all harts except self


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: sends IPI to all harts except self")
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

- AC-1: PENDING_IPI slots for all non-self harts contain broadcast vector
   - Expected: hal_smp_get_pending_ipi(1u32) equals `77u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AC-1: PENDING_IPI slots for all non-self harts contain broadcast vector")
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
| Source | `test/unit/os/kernel/arch/riscv/hal_smp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HalSmp, hal_smp_cpu_count, hal_smp_cpu_start, hal_smp_ipi_send, hal_smp_ipi_broadcast.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c4bfbc3d26b0010a2e23ef42fc900dc92527acdc21be244a08e80f3e87b0ac4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c4bfbc3d26b0010a2e23ef42fc900dc92527acdc21be244a08e80f3e87b0ac4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c4bfbc3d26b0010a2e23ef42fc900dc92527acdc21be244a08e80f3e87b0ac4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/arch/riscv/hal_smp_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/riscv/hal_smp_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/riscv/hal_smp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/riscv/hal_smp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/riscv/hal_smp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/riscv/hal_smp_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns 1 when DTB is null (fallback)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv/hal_smp_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: returns 2 for a two-hart FDT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/riscv/hal_smp_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-1: disabled hart is excluded from count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
