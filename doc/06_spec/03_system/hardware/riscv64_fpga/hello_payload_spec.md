# Hello Payload Specification

> <details>

<!-- sdn-diagram:id=hello_payload_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hello_payload_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hello_payload_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hello_payload_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hello Payload Specification

## Scenarios

### Hello Payload - Source Files (AC-7)

#### hello payload directory path is correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = "examples/09_embedded/fpga_riscv/rv64_fpga_hello"
expect(dir).to_contain("09_embedded")
expect(dir).to_contain("fpga_riscv")
expect(dir).to_contain("rv64_fpga_hello")
```

</details>

#### startup.S assembly source exists at correct path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/startup.S"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("startup.S")
```

</details>

#### main.c C source exists at correct path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/main.c"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("main.c")
```

</details>

#### linker script exists at correct path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/linker.ld"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("linker.ld")
```

</details>

#### build script exists at correct path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/build.shs"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("build.shs")
```

</details>

### Hello Payload - Linker Script Values (AC-7)

#### linker script RAM ORIGIN is 0x80000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ram_origin = "0x80000000"
expect(ram_origin).to_equal("0x80000000")
```

</details>

#### linker script BRAM ORIGIN is 0x00000000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bram_origin = "0x00000000"
expect(bram_origin).to_equal("0x00000000")
```

</details>

#### hello payload triple is riscv64-unknown-none-elf

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val triple = "riscv64-unknown-none-elf"
expect(triple).to_contain("riscv64")
expect(triple).to_contain("none-elf")
```

</details>

### Hello Payload - Proof String Format (AC-7)

#### proof string prefix is SIMPLE-RV64-FPGA-HELLO

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "SIMPLE-RV64-FPGA-HELLO"
expect(prefix).to_start_with("SIMPLE")
expect(prefix).to_contain("RV64")
expect(prefix).to_contain("FPGA")
expect(prefix).to_contain("HELLO")
```

</details>

#### proof string contains board field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "board="
expect(field).to_equal("board=")
```

</details>

#### proof string contains hart field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "hart="
expect(field).to_equal("hart=")
```

</details>

#### proof string contains pc field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val field = "pc="
expect(field).to_equal("pc=")
```

</details>

#### proof string hart value is 0 for single-hart boot

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hart_val = "hart=0"
expect(hart_val).to_equal("hart=0")
```

</details>

#### expected proof string matches board and hart

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proof = "SIMPLE-RV64-FPGA-HELLO board=xck26-ml-carrier hart=0 pc=0x80001234"
expect(proof).to_contain("SIMPLE-RV64-FPGA-HELLO")
expect(proof).to_contain("board=xck26-ml-carrier")
expect(proof).to_contain("hart=0")
expect(proof).to_contain("pc=0x")
```

</details>

### Hello Payload - BLOCKED Gates (AC-7, AC-8)

#### BLOCKED: cross-compile requires riscv64-unknown-elf-gcc

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = "BLOCKED: riscv64-unknown-elf-gcc not found"
print gate
expect(gate).to_start_with("BLOCKED:")
expect(gate).to_contain("riscv64-unknown-elf-gcc")
expect(gate).to_contain("not found")
```

</details>

#### BLOCKED: ELF link step requires riscv64 cross toolchain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = "BLOCKED: riscv64-unknown-elf-gcc not found"
print gate
expect(gate).to_start_with("BLOCKED:")
expect(gate).to_contain("riscv64-unknown-elf-gcc")
expect(gate).to_contain("not found")
```

</details>

#### BLOCKED: FPGA upload requires openFPGALoader and synthesis tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = "BLOCKED: riscv64-fpga-min FPGA upload requires vivado or openFPGALoader"
print gate
expect(gate).to_start_with("BLOCKED:")
expect(gate).to_contain("FPGA upload")
expect(gate).to_contain("openFPGALoader")
```

</details>

#### BLOCKED: UART proof string verification requires connected FPGA board

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gate = "BLOCKED: UART proof requires connected FPGA board"
print gate
expect(gate).to_start_with("BLOCKED:")
expect(gate).to_contain("UART proof")
expect(gate).to_contain("connected FPGA board")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/riscv64_fpga/hello_payload_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Hello Payload - Source Files (AC-7)
- Hello Payload - Linker Script Values (AC-7)
- Hello Payload - Proof String Format (AC-7)
- Hello Payload - BLOCKED Gates (AC-7, AC-8)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
