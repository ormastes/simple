# Riscv64 Trap Frame Specification

> <details>

<!-- sdn-diagram:id=riscv64_trap_frame_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_trap_frame_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_trap_frame_spec -> std
riscv64_trap_frame_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_trap_frame_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Trap Frame Specification

## Scenarios

### rv64 trap frame layout

#### uses 8-byte slots for each saved field

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RV64_TRAP_FRAME_SLOT_BYTES).to_equal(8)
```

</details>

#### reports the full saved frame size

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RV64_TRAP_FRAME_FIELD_COUNT).to_equal(34)
expect(RV64_TRAP_FRAME_SIZE_BYTES).to_equal(272)
```

</details>

#### keeps key register offsets stable

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RV64_TRAP_RA_OFFSET).to_equal(0)
expect(RV64_TRAP_SP_OFFSET).to_equal(8)
expect(RV64_TRAP_A0_OFFSET).to_equal(72)
expect(RV64_TRAP_A7_OFFSET).to_equal(128)
expect(RV64_TRAP_SEPC_OFFSET).to_equal(248)
expect(RV64_TRAP_SSTATUS_OFFSET).to_equal(256)
expect(RV64_TRAP_SCAUSE_OFFSET).to_equal(264)
```

</details>

#### returns a monotonic ordered field list

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offsets = rv64_trap_frame_field_offsets()
expect(offsets.len()).to_equal(34)

var i = 1
while i < offsets.len():
    expect(offsets[i]).to_equal(offsets[i - 1] + RV64_TRAP_FRAME_SLOT_BYTES)
    i = i + 1
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64_trap_frame_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rv64 trap frame layout

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
