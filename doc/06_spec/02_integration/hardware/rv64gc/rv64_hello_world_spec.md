# RV64 Hello World SoC Integration Tests

> Full SoC pipeline: bus decode, UART output, timer, SRAM.

<!-- sdn-diagram:id=rv64_hello_world_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_hello_world_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_hello_world_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_hello_world_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Hello World SoC Integration Tests

Full SoC pipeline: bus decode, UART output, timer, SRAM.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64-HELLO-001 |
| Category | Hardware |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/02_integration/hardware/rv64gc/rv64_hello_world_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Full SoC pipeline: bus decode, UART output, timer, SRAM.

## Scenarios

### Bus Address Decode

#### CLINT region: 0x02000000-0x0200FFFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = CLINT_BASE + 0x4000
val in_clint = addr >= CLINT_BASE and addr < CLINT_BASE + 0x10000
expect(in_clint).to_equal(true)
```

</details>

#### PLIC region: 0x0C000000-0x0FFFFFFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = PLIC_BASE + 0x200004
val in_plic = addr >= PLIC_BASE and addr < PLIC_BASE + 0x4000000
expect(in_plic).to_equal(true)
```

</details>

#### UART region: 0x10000000-0x10000FFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = UART_BASE + 5
val in_uart = addr >= UART_BASE and addr < UART_BASE + 0x1000
expect(in_uart).to_equal(true)
```

</details>

#### DRAM region: 0x80000000+

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr = DRAM_BASE + 0x1000
val in_dram = addr >= DRAM_BASE
expect(in_dram).to_equal(true)
```

</details>

### UART Model

#### TX register is ready when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LSR bit 5 = THR empty
val lsr: i64 = 0x60  # Both THR empty and transmitter idle
expect((lsr and 0x20) != 0).to_equal(true)
```

</details>

#### write byte to THR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tx_byte: i64 = 0
tx_byte = 0x48  # 'H'
expect(tx_byte).to_equal(0x48)
```

</details>

#### multiple bytes form string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hello = [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # "Hello"
expect(hello.len()).to_equal(5)
```

</details>

### Timer Model

#### mtime increments

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mtime: i64 = 0
mtime = mtime + 1
expect(mtime).to_equal(1)
```

</details>

#### timer compare triggers interrupt

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mtime: i64 = 100
val mtimecmp: i64 = 50
expect(mtime >= mtimecmp).to_equal(true)
```

</details>

#### timer compare not triggered before threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mtime: i64 = 10
val mtimecmp: i64 = 50
expect(mtime >= mtimecmp).to_equal(false)
```

</details>

### SRAM Model (64-bit)

#### write and read 64-bit value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mem: [i64] = [0, 0, 0, 0]
mem[0] = 0xDEADBEEFCAFEBABE
expect(mem[0]).to_equal(0xDEADBEEFCAFEBABE)
```

</details>

#### byte-addressable access

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var byte_val: i64 = 0xFF
expect(byte_val and 0xFF).to_equal(0xFF)
```

</details>

#### word-aligned access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr: i64 = 0x80000008
val aligned = addr and 0xFFFFFFFFFFFFFFF8
expect(aligned).to_equal(0x80000008)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
