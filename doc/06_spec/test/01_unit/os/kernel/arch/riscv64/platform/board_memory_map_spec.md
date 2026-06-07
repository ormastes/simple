# RiscvBoardMemoryMap Trait Specification

> Verifies AC-5: RiscvBoardMemoryMap trait and its two concrete implementations (KriaFpgaMemoryMap for K26, LitexFpgaMemoryMap for DE10-Nano) return correct address constants. These constants gate the minimal-host boot chain.

<!-- sdn-diagram:id=board_memory_map_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=board_memory_map_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

board_memory_map_spec -> std
board_memory_map_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=board_memory_map_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RiscvBoardMemoryMap Trait Specification

Verifies AC-5: RiscvBoardMemoryMap trait and its two concrete implementations (KriaFpgaMemoryMap for K26, LitexFpgaMemoryMap for DE10-Nano) return correct address constants. These constants gate the minimal-host boot chain.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | opensource-riscv-rtl-simpleos |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Draft |
| Requirements | REQ-5 |
| Source | `test/01_unit/os/kernel/arch/riscv64/platform/board_memory_map_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies AC-5: RiscvBoardMemoryMap trait and its two concrete implementations
(KriaFpgaMemoryMap for K26, LitexFpgaMemoryMap for DE10-Nano) return correct
address constants. These constants gate the minimal-host boot chain.

Covers:
- AC-5 (SimpleOS boots with correct memory map: UART, RAM, heap, CLINT, PLIC)

## Scenarios

### KriaFpgaMemoryMap

#### AC-5: uart_base returns 0x10000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = kria_map()
expect(m.uart_base()).to_equal(268435456)
```

</details>

#### AC-5: ram_base returns 0x80000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = kria_map()
expect(m.ram_base()).to_equal(2147483648)
```

</details>

#### AC-5: ram_size returns 128MB (134217728 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = kria_map()
expect(m.ram_size()).to_equal(134217728)
```

</details>

#### AC-5: clint_base returns 0x02000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = kria_map()
expect(m.clint_base()).to_equal(33554432)
```

</details>

#### AC-5: plic_base returns 0x0c000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = kria_map()
expect(m.plic_base()).to_equal(201326592)
```

</details>

#### AC-5: heap_start returns 0x87000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = kria_map()
expect(m.heap_start()).to_equal(2264924160)
```

</details>

#### AC-5: heap_size is 16MB (16777216 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = kria_map()
expect(m.heap_size()).to_equal(16777216)
```

</details>

### LitexFpgaMemoryMap

#### AC-5: uart_base returns 0xf0001000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = litex_map()
expect(m.uart_base()).to_equal(4026535936)
```

</details>

#### AC-5: ram_base returns 0x40000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = litex_map()
expect(m.ram_base()).to_equal(1073741824)
```

</details>

#### AC-5: ram_size returns 256MB (268435456 bytes)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = litex_map()
expect(m.ram_size()).to_equal(268435456)
```

</details>

#### AC-5: clint_base returns 0xf0010000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = litex_map()
expect(m.clint_base()).to_equal(4026597376)
```

</details>

#### AC-5: plic_base returns 0xf0c00000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = litex_map()
expect(m.plic_base()).to_equal(4039114752)
```

</details>

#### AC-5: heap_start returns 0x4f000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = litex_map()
expect(m.heap_start()).to_equal(1325400064)
```

</details>

#### AC-5: LiteX and Kria uart_base are different

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kria = kria_map()
val litex = litex_map()
val kria_uart = kria.uart_base()
val litex_uart = litex.uart_base()
expect(kria_uart).to_equal(268435456)
expect(litex_uart).to_equal(4026535936)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [REQ-5](REQ-5)


</details>
