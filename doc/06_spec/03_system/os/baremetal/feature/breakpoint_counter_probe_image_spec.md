# Breakpoint Counter Probe Image Specification

> <details>

<!-- sdn-diagram:id=breakpoint_counter_probe_image_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakpoint_counter_probe_image_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakpoint_counter_probe_image_spec -> std
breakpoint_counter_probe_image_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakpoint_counter_probe_image_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakpoint Counter Probe Image Specification

## Scenarios

### Bare-metal Breakpoint Probe Image Contract

### architecture matrix

#### should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = breakpoint_probe_image_arches()
expect(arches).to_contain("i386")
expect(arches).to_contain("x86_64")
expect(arches).to_contain("arm32")
expect(arches).to_contain("thumb")
expect(arches).to_contain("aarch64")
expect(arches).to_contain("riscv32")
expect(arches).to_contain("riscv32c")
expect(arches).to_contain("riscv64")
expect(arches).to_contain("riscv64c")
```

</details>

#### should derive deterministic source output linker compiler and serial driver paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_probe_image_build_dir("x86_64")).to_equal("build/baremetal/breakpoint_probe/x86_64")
expect(breakpoint_probe_image_source_path("x86_64")).to_equal("build/baremetal/breakpoint_probe/x86_64/breakpoint_probe.c")
expect(breakpoint_probe_image_output_path("riscv64c")).to_equal("build/baremetal/breakpoint_probe/riscv64c/breakpoint_probe.elf")
expect(breakpoint_probe_image_linker_script_path("i386")).to_equal("build/baremetal/breakpoint_probe/i386/breakpoint_probe.ld")
expect(breakpoint_probe_image_linker_script_path("aarch64")).to_equal("build/baremetal/breakpoint_probe/aarch64/breakpoint_probe.ld")
expect(breakpoint_probe_image_linker_script_path("riscv32c")).to_equal("build/baremetal/breakpoint_probe/riscv32c/breakpoint_probe.ld")
expect(breakpoint_probe_image_compiler("thumb")).to_equal("clang")
expect(breakpoint_probe_image_compiler("aarch64")).to_equal("clang")
expect(breakpoint_probe_image_compiler("riscv64")).to_equal("riscv64-unknown-elf-gcc")
expect(breakpoint_probe_image_serial_driver("x86_64")).to_equal("com1")
expect(breakpoint_probe_image_serial_driver("arm32")).to_equal("pl011")
expect(breakpoint_probe_image_serial_driver("riscv64c")).to_equal("ns16550")
```

</details>

### build and run readiness

#### should fail closed until source compiler and ELF evidence are present

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_source = breakpoint_probe_image_plan("riscv64", false, false, true)
expect(missing_source.can_run).to_equal(false)
expect(missing_source.status).to_equal("missing_probe_source")

val missing_compiler = breakpoint_probe_image_plan("riscv64", true, false, false)
expect(missing_compiler.can_run).to_equal(false)
expect(missing_compiler.status).to_equal("compiler_unavailable")

val missing_elf = breakpoint_probe_image_plan("riscv64", true, false, true)
expect(missing_elf.can_build).to_equal(true)
expect(missing_elf.can_run).to_equal(false)
expect(missing_elf.status).to_equal("missing_probe_elf")

val ready = breakpoint_probe_image_plan("riscv64c", true, true, true)
expect(ready.can_run).to_equal(true)
expect(ready.status).to_equal("ready")
expect(ready.qemu_binary).to_equal("qemu-system-riscv64")
expect(ready.required_evidence_fields).to_contain("icache")
```

</details>

#### should emit compiler arguments with the expected linker and output paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = breakpoint_probe_image_build_args("x86_64")
expect(x86).to_contain("-m32")
expect(x86).to_contain("-no-pie")
expect(x86).to_contain("-nostdlib")
expect(x86).to_contain("build/baremetal/breakpoint_probe/x86_64/breakpoint_probe.c")
expect(x86).to_contain("-o")
expect(x86).to_contain("build/baremetal/breakpoint_probe/x86_64/breakpoint_probe.elf")

val thumb = breakpoint_probe_image_build_args("thumb")
expect(thumb).to_contain("--target=arm-none-eabi")
expect(thumb).to_contain("-mcpu=cortex-a15")
expect(thumb).to_contain("-mthumb")
expect(thumb).to_contain("-Wl,-T,build/baremetal/breakpoint_probe/thumb/breakpoint_probe.ld")

val aarch64 = breakpoint_probe_image_build_args("aarch64")
expect(aarch64).to_contain("--target=aarch64-none-elf")
expect(aarch64).to_contain("-Wl,-T,build/baremetal/breakpoint_probe/aarch64/breakpoint_probe.ld")

val rv32c = breakpoint_probe_image_build_args("riscv32c")
expect(rv32c).to_contain("-march=rv32imac_zifencei")
expect(rv32c).to_contain("-mabi=ilp32")
expect(rv32c).to_contain("-mcmodel=medany")
```

</details>

### serial evidence contract

#### should require every field consumed by the QEMU evidence parser

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = breakpoint_probe_required_evidence_fields()
expect(fields).to_contain("arch")
expect(fields).to_contain("qemu")
expect(fields).to_contain("address")
expect(fields).to_contain("original")
expect(fields).to_contain("trap")
expect(fields).to_contain("hits")
expect(fields).to_contain("latency_us")
expect(fields).to_contain("restored")
expect(fields).to_contain("rearmed")
expect(fields).to_contain("cleanup")
expect(fields).to_contain("icache")
expect(fields).to_contain("sampled")
```

</details>

#### should generate architecture-specific serial evidence templates

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = breakpoint_probe_serial_evidence_contract_line("x86_64")
expect(x86).to_start_with("simple-breakpoint-evidence;")
expect(x86).to_contain("arch=x86_64")
expect(x86).to_contain("trap=cc")
expect(x86).to_contain("icache=false")

val rvc = breakpoint_probe_serial_evidence_contract_line("riscv64c")
expect(rvc).to_contain("arch=riscv64c")
expect(rvc).to_contain("trap=02 90")
expect(rvc).to_contain("icache=true")
```

</details>

#### should generate parser-valid runtime serial evidence for staged probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = breakpoint_probe_serial_evidence_runtime_line("riscv64c")
expect(runtime).to_start_with("simple-breakpoint-evidence;")
expect(runtime).to_contain("arch=riscv64c")
expect(runtime).to_contain("address=1048576")
expect(runtime).to_contain("original=01 00")
expect(runtime).to_contain("trap=02 90")
expect(runtime).to_contain("hits=1")
expect(runtime).to_contain("latency_us=1")
expect(runtime).to_contain("restored=true")
expect(runtime).to_contain("rearmed=true")
expect(runtime).to_contain("cleanup=true")
expect(runtime).to_contain("icache=true")
expect(runtime).to_contain("sampled=none")
```

</details>

#### should produce source contract text that records trap and evidence requirements

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = breakpoint_probe_source_contract_text("aarch64")
expect(source).to_contain("simple-breakpoint-probe-source-v1")
expect(source).to_contain("arch=aarch64")
expect(source).to_contain("trap=brk-imm0")
expect(source).to_contain("bytes=00 00 20 d4")
expect(source).to_contain("simple-breakpoint-evidence;arch=aarch64")
```

</details>

### generated probe source artifact

#### should define original instruction bytes for native patch restore coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_probe_original_instruction_bytes("x86_64")).to_equal("90")
expect(breakpoint_probe_original_instruction_bytes("thumb")).to_equal("00 bf")
expect(breakpoint_probe_original_instruction_bytes("aarch64")).to_equal("1f 20 03 d5")
expect(breakpoint_probe_original_instruction_bytes("riscv64c")).to_equal("01 00")
```

</details>

#### should define architecture serial writes for QEMU serial output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_probe_serial_putc_body("x86_64")).to_contain("outb")
expect(breakpoint_probe_serial_putc_body("arm32")).to_contain("0x09000000")
expect(breakpoint_probe_serial_putc_body("aarch64")).to_contain("0x09000000")
expect(breakpoint_probe_serial_putc_body("riscv64c")).to_contain("0x10000000")
```

</details>

#### should define freestanding icache flushes without runtime library calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_probe_icache_flush_body("x86_64")).to_contain("memory")
expect(breakpoint_probe_icache_flush_body("arm32")).to_contain("dsb sy")
expect(breakpoint_probe_icache_flush_body("aarch64")).to_contain("isb")
expect(breakpoint_probe_icache_flush_body("riscv64c")).to_contain("fence.i")
```

</details>

#### should define boot entry shims for QEMU-loaded probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_probe_entry_asm_text("i386")).to_contain(".multiboot")
expect(breakpoint_probe_entry_asm_text("i386")).to_contain(".note.Xen")
expect(breakpoint_probe_entry_asm_text("i386")).to_contain(".long 18")
expect(breakpoint_probe_entry_asm_text("x86_64")).to_contain("_entry32")
expect(breakpoint_probe_entry_asm_text("thumb")).to_contain(".arm")
expect(breakpoint_probe_entry_asm_text("thumb")).to_contain("ldr r0, =probe_main")
expect(breakpoint_probe_entry_asm_text("thumb")).to_contain("bx r0")
expect(breakpoint_probe_entry_asm_text("riscv64c")).to_contain("la sp, simple_probe_stack_top")
expect(breakpoint_probe_entry_asm_text("aarch64")).to_contain("mov sp, x0")
```

</details>

#### should generate freestanding C that patches traps restores rearms and emits evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = breakpoint_probe_source_text("riscv64c")
expect(source).to_contain("simple-breakpoint-probe-source-v1")
expect(source).to_contain(".section .text.entry")
expect(source).to_contain("static volatile uint8_t simple_probe_instruction[2]")
expect(source).to_contain("static const uint8_t simple_probe_trap[2] = {0x02, 0x90};")
expect(source).to_contain("static const uint8_t simple_probe_original[2] = {0x01, 0x00};")
expect(source).to_contain("static void serial_putc(char c)\n{\n  (*(volatile uint8_t *)0x10000000u) = (uint8_t)c;\n}")
expect(source).to_contain("0x10000000")
expect(source).to_contain("fence.i")
expect(source).to_contain("probe_copy(simple_probe_instruction, simple_probe_trap);")
expect(source).to_contain("probe_copy(simple_probe_instruction, simple_probe_original);")
expect(source).to_contain("void probe_main(void)")
expect(source).to_contain("simple-breakpoint-evidence;arch=riscv64c")
expect(source).to_contain(";hits=1;")
expect(source).to_contain(";sampled=none")
expect(source).to_contain("simple-breakpoint-probe-native-contract arch=riscv64c")
```

</details>

#### should package source artifacts with deterministic build locations

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = breakpoint_probe_source_artifact("thumb")
expect(artifact.valid).to_equal(true)
expect(artifact.status).to_equal("ready")
expect(artifact.build_dir).to_equal("build/baremetal/breakpoint_probe/thumb")
expect(artifact.source_path).to_equal("build/baremetal/breakpoint_probe/thumb/breakpoint_probe.c")
expect(artifact.source_text).to_contain("arch=thumb")
expect(artifact.source_text).to_contain("static const uint8_t simple_probe_trap[2] = {0x00, 0xbe};")
```

</details>

#### should generate probe-specific linker scripts without full kernel symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86_linker = breakpoint_probe_linker_script_text("x86_64")
expect(x86_linker).to_contain("ENTRY(_entry32)")
expect(x86_linker).to_contain("KEEP(*(.multiboot))")
expect(x86_linker).to_contain("simple_probe_stack_top")
expect(x86_linker.contains("kernel__arch__x86_64")).to_equal(false)

val riscv_linker = breakpoint_probe_linker_script_text("riscv64c")
expect(riscv_linker).to_contain("OUTPUT_FORMAT(\"elf64-littleriscv\")")
expect(riscv_linker).to_contain("ENTRY(_start)")
val rv32_linker = breakpoint_probe_linker_script_text("riscv32c")
expect(rv32_linker).to_contain("OUTPUT_FORMAT(\"elf32-littleriscv\")")
expect(rv32_linker).to_contain(". = 0x80000000")
val artifact = breakpoint_probe_linker_artifact("riscv64c")
expect(artifact.valid).to_equal(true)
expect(artifact.linker_script_path).to_equal("build/baremetal/breakpoint_probe/riscv64c/breakpoint_probe.ld")
```

</details>

#### should package every supported architecture for staging

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifacts = breakpoint_probe_source_artifacts()
expect(artifacts.len()).to_equal(9)
expect(artifacts[0].source_path).to_equal("build/baremetal/breakpoint_probe/i386/breakpoint_probe.c")
expect(artifacts[8].source_path).to_equal("build/baremetal/breakpoint_probe/riscv64c/breakpoint_probe.c")
expect(artifacts[8].source_text).to_contain("hits=1")
```

</details>

#### should make all-arch staging idempotent

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = breakpoint_probe_stage_all_sources()
val second = breakpoint_probe_stage_all_sources()
expect(first.requested_count).to_equal(9)
expect(second.requested_count).to_equal(9)
expect(second.written_count).to_equal(9)
expect(second.failed_count).to_equal(0)
expect(second.status).to_equal("written")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bare-metal Breakpoint Probe Image Contract
- architecture matrix
- build and run readiness
- serial evidence contract
- generated probe source artifact

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
