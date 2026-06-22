# RiscvNoallocHandoff Memory Map Parameterization Specification

> Verifies AC-6: riscv_noalloc_handoff accepts board-specific layouts through the RISC-V64 arch adapter so the boot chain works for both K26 (Kria) and DE10-Nano (LiteX) without hard-coded addresses in the handoff module. Tests that the layout struct produced for each board has correct fields.

<!-- sdn-diagram:id=riscv_noalloc_handoff_vexriscv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_noalloc_handoff_vexriscv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_noalloc_handoff_vexriscv_spec -> std
riscv_noalloc_handoff_vexriscv_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_noalloc_handoff_vexriscv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RiscvNoallocHandoff Memory Map Parameterization Specification

Verifies AC-6: riscv_noalloc_handoff accepts board-specific layouts through the RISC-V64 arch adapter so the boot chain works for both K26 (Kria) and DE10-Nano (LiteX) without hard-coded addresses in the handoff module. Tests that the layout struct produced for each board has correct fields.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-6 |
| Source | `test/01_unit/os/kernel/boot/riscv_noalloc_handoff_vexriscv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-6: riscv_noalloc_handoff accepts board-specific layouts through the
RISC-V64 arch adapter so the boot chain works for both K26 (Kria) and
DE10-Nano (LiteX) without hard-coded addresses in the handoff module. Tests
that the layout struct produced for each board has correct fields.

Covers:
- AC-6 (Scheduler/handoff parameterization for real-hardware idle loop)

## Scenarios

### RiscvNoallocHandoff Kria layout

#### AC-6: Kria layout uart_base matches KriaFpgaMemoryMap

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = kria_layout()
expect(layout.uart_base).to_equal(268435456)
```

</details>

#### AC-6: Kria layout ram_base is 0x80000000

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = kria_layout()
expect(layout.ram_base).to_equal(2147483648)
```

</details>

#### AC-6: Kria layout heap_start is 0x87000000

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = kria_layout()
expect(layout.heap_start).to_equal(2264924160)
```

</details>

#### AC-6: Kria layout heap_size is 16MB

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = kria_layout()
expect(layout.heap_size).to_equal(16777216)
```

</details>

### RiscvNoallocHandoff LiteX layout

#### AC-6: LiteX layout uart_base is 0xf0001000

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = litex_layout()
expect(layout.uart_base).to_equal(4026535936)
```

</details>

#### AC-6: LiteX layout ram_base is 0x40000000

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = litex_layout()
expect(layout.ram_base).to_equal(1073741824)
```

</details>

#### AC-6: LiteX layout heap_start is 0x4f000000

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val layout = litex_layout()
expect(layout.heap_start).to_equal(1325400064)
```

</details>

#### AC-6: LiteX and Kria uart_base differ

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kria = kria_layout()
val litex = litex_layout()
expect(kria.uart_base).to_equal(268435456)
expect(litex.uart_base).to_equal(4026535936)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-6](REQ-6)


</details>
