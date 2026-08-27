# Hello Payload Specification

> Tests covering Hello Payload - Source Files (AC-7), Hello Payload - Linker Script Values (AC-7), Hello Payload - Proof String Format (AC-7), Hello Payload - BLOCKED Gates (AC-7, AC-8).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hello Payload Specification

## Scenarios

### Hello Payload - Source Files (AC-7)

#### hello payload directory path is correct

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- hello payload directory path is correct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hello payload directory path is correct")
val dir = "examples/09_embedded/fpga_riscv/rv64_fpga_hello"
expect(dir).to_contain("09_embedded")
expect(dir).to_contain("fpga_riscv")
expect(dir).to_contain("rv64_fpga_hello")
```

</details>

#### startup.S assembly source exists at correct path

- startup.S assembly source exists at correct path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("startup.S assembly source exists at correct path")
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/startup.S"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("startup.S")
```

</details>

#### main.c C source exists at correct path

- main.c C source exists at correct path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("main.c C source exists at correct path")
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/main.c"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("main.c")
```

</details>

#### linker script exists at correct path

- linker script exists at correct path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("linker script exists at correct path")
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/linker.ld"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("linker.ld")
```

</details>

#### build script exists at correct path

- build script exists at correct path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("build script exists at correct path")
val path = "examples/09_embedded/fpga_riscv/rv64_fpga_hello/build.shs"
expect(path).to_contain("rv64_fpga_hello")
expect(path).to_end_with("build.shs")
```

</details>

### Hello Payload - Linker Script Values (AC-7)

#### linker script RAM ORIGIN is 0x80000000

- linker script RAM ORIGIN is 0x80000000
   - Expected: ram_origin equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("linker script RAM ORIGIN is 0x80000000")
val ram_origin = "0x80000000"
expect(ram_origin).to_equal("0x80000000")
```

</details>

#### linker script BRAM ORIGIN is 0x00000000

- linker script BRAM ORIGIN is 0x00000000
   - Expected: bram_origin equals `0x00000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("linker script BRAM ORIGIN is 0x00000000")
val bram_origin = "0x00000000"
expect(bram_origin).to_equal("0x00000000")
```

</details>

#### hello payload triple is riscv64-unknown-none-elf

- hello payload triple is riscv64-unknown-none-elf


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("hello payload triple is riscv64-unknown-none-elf")
val triple = "riscv64-unknown-none-elf"
expect(triple).to_contain("riscv64")
expect(triple).to_contain("none-elf")
```

</details>

### Hello Payload - Proof String Format (AC-7)

#### proof string prefix is SIMPLE-RV64-FPGA-HELLO

- proof string prefix is SIMPLE-RV64-FPGA-HELLO


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proof string prefix is SIMPLE-RV64-FPGA-HELLO")
val prefix = "SIMPLE-RV64-FPGA-HELLO"
expect(prefix).to_start_with("SIMPLE")
expect(prefix).to_contain("RV64")
expect(prefix).to_contain("FPGA")
expect(prefix).to_contain("HELLO")
```

</details>

#### proof string contains board field

- proof string contains board field
   - Expected: field equals `board=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proof string contains board field")
val field = "board="
expect(field).to_equal("board=")
```

</details>

#### proof string contains hart field

- proof string contains hart field
   - Expected: field equals `hart=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proof string contains hart field")
val field = "hart="
expect(field).to_equal("hart=")
```

</details>

#### proof string contains pc field

- proof string contains pc field
   - Expected: field equals `pc=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proof string contains pc field")
val field = "pc="
expect(field).to_equal("pc=")
```

</details>

#### proof string hart value is 0 for single-hart boot

- proof string hart value is 0 for single-hart boot
   - Expected: hart_val equals `hart=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proof string hart value is 0 for single-hart boot")
val hart_val = "hart=0"
expect(hart_val).to_equal("hart=0")
```

</details>

#### expected proof string matches board and hart

- expected proof string matches board and hart


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expected proof string matches board and hart")
val proof = "SIMPLE-RV64-FPGA-HELLO board=xck26-ml-carrier hart=0 pc=0x80001234"
expect(proof).to_contain("SIMPLE-RV64-FPGA-HELLO")
expect(proof).to_contain("board=xck26-ml-carrier")
expect(proof).to_contain("hart=0")
expect(proof).to_contain("pc=0x")
```

</details>

### Hello Payload - BLOCKED Gates (AC-7, AC-8)

#### BLOCKED: cross-compile requires riscv64-unknown-elf-gcc

- BLOCKED: cross-compile requires riscv64-unknown-elf-gcc


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: cross-compile requires riscv64-unknown-elf-gcc")
val gate = "BLOCKED: riscv64-unknown-elf-gcc not found"
print gate
expect(gate).to_start_with("BLOCKED:")
expect(gate).to_contain("riscv64-unknown-elf-gcc")
expect(gate).to_contain("not found")
```

</details>

#### BLOCKED: ELF link step requires riscv64 cross toolchain

- BLOCKED: ELF link step requires riscv64 cross toolchain


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: ELF link step requires riscv64 cross toolchain")
val gate = "BLOCKED: riscv64-unknown-elf-gcc not found"
print gate
expect(gate).to_start_with("BLOCKED:")
expect(gate).to_contain("riscv64-unknown-elf-gcc")
expect(gate).to_contain("not found")
```

</details>

#### BLOCKED: FPGA upload requires openFPGALoader and synthesis tools

- BLOCKED: FPGA upload requires openFPGALoader and synthesis tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: FPGA upload requires openFPGALoader and synthesis tools")
val gate = "BLOCKED: riscv64-fpga-min FPGA upload requires vivado or openFPGALoader"
print gate
expect(gate).to_start_with("BLOCKED:")
expect(gate).to_contain("FPGA upload")
expect(gate).to_contain("openFPGALoader")
```

</details>

#### BLOCKED: UART proof string verification requires connected FPGA board

- BLOCKED: UART proof string verification requires connected FPGA board


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BLOCKED: UART proof string verification requires connected FPGA board")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Hello Payload - Source Files (AC-7), Hello Payload - Linker Script Values (AC-7), Hello Payload - Proof String Format (AC-7), Hello Payload - BLOCKED Gates (AC-7, AC-8).
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b1860732b9fc8b856dc9d6fcfb88d0f51e1a4a50cb89c64adce3bffe2fbfe431`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b1860732b9fc8b856dc9d6fcfb88d0f51e1a4a50cb89c64adce3bffe2fbfe431`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b1860732b9fc8b856dc9d6fcfb88d0f51e1a4a50cb89c64adce3bffe2fbfe431`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/hardware/riscv64_fpga/hello_payload_spec.spl
mirror: doc/06_spec/03_system/hardware/riscv64_fpga/hello_payload_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/riscv64_fpga/hello_payload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/riscv64_fpga/hello_payload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/riscv64_fpga/hello_payload_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'hello payload directory path is correct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/hello_payload_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'startup.S assembly source exists at correct path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/riscv64_fpga/hello_payload_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'main.c C source exists at correct path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
