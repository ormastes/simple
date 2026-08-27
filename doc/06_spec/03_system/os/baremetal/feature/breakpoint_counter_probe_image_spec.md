# breakpoint_counter_probe_image_spec

> Purpose: should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# breakpoint_counter_probe_image_spec

Purpose: should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets
Audience: compiler and tooling engineers who maintain this spec

## Scenarios

### Bare-metal Breakpoint Probe Image Contract

### architecture matrix

#### should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets

- should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets
- Verify: should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets")
step("Verify: should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets")
# @req: REQ-OS-BreaCounProbImag-001
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

- should derive deterministic source output linker compiler and serial driver paths
- Verify: should derive deterministic source output linker compiler and serial driver paths
   - Expected: breakpoint_probe_image_build_dir("x86_64") equals `build/baremetal/breakpoint_probe/x86_64`
   - Expected: breakpoint_probe_image_source_path("x86_64") equals `build/baremetal/breakpoint_probe/x86_64/breakpoint_probe.c`
   - Expected: breakpoint_probe_image_output_path("riscv64c") equals `build/baremetal/breakpoint_probe/riscv64c/breakpoint_probe.elf`
   - Expected: breakpoint_probe_image_linker_script_path("i386") equals `build/baremetal/breakpoint_probe/i386/breakpoint_probe.ld`
   - Expected: breakpoint_probe_image_linker_script_path("aarch64") equals `build/baremetal/breakpoint_probe/aarch64/breakpoint_probe.ld`
   - Expected: breakpoint_probe_image_linker_script_path("riscv32c") equals `build/baremetal/breakpoint_probe/riscv32c/breakpoint_probe.ld`
   - Expected: breakpoint_probe_image_compiler("thumb") equals `clang`
   - Expected: breakpoint_probe_image_compiler("aarch64") equals `clang`
   - Expected: breakpoint_probe_image_compiler("riscv64") equals `riscv64-unknown-elf-gcc`
   - Expected: breakpoint_probe_image_serial_driver("x86_64") equals `com1`
   - Expected: breakpoint_probe_image_serial_driver("arm32") equals `pl011`
   - Expected: breakpoint_probe_image_serial_driver("riscv64c") equals `ns16550`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should derive deterministic source output linker compiler and serial driver paths")
step("Verify: should derive deterministic source output linker compiler and serial driver paths")
# @req: REQ-OS-BreaCounProbImag-001
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

- should fail closed until source compiler and ELF evidence are present
- Verify: should fail closed until source compiler and ELF evidence are present
   - Expected: missing_source.can_run is false
   - Expected: missing_source.status equals `missing_probe_source`
   - Expected: missing_compiler.can_run is false
   - Expected: missing_compiler.status equals `compiler_unavailable`
   - Expected: missing_elf.can_build is true
   - Expected: missing_elf.can_run is false
   - Expected: missing_elf.status equals `missing_probe_elf`
   - Expected: ready.can_run is true
   - Expected: ready.status equals `ready`
   - Expected: ready.qemu_binary equals `qemu-system-riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should fail closed until source compiler and ELF evidence are present")
step("Verify: should fail closed until source compiler and ELF evidence are present")
# @req: REQ-OS-BreaCounProbImag-001
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

- should emit compiler arguments with the expected linker and output paths
- Verify: should emit compiler arguments with the expected linker and output paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit compiler arguments with the expected linker and output paths")
step("Verify: should emit compiler arguments with the expected linker and output paths")
# @req: REQ-OS-BreaCounProbImag-001
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

- should require every field consumed by the QEMU evidence parser
- Verify: should require every field consumed by the QEMU evidence parser


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should require every field consumed by the QEMU evidence parser")
step("Verify: should require every field consumed by the QEMU evidence parser")
# @req: REQ-OS-BreaCounProbImag-001
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

- should generate architecture-specific serial evidence templates
- Verify: should generate architecture-specific serial evidence templates


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate architecture-specific serial evidence templates")
step("Verify: should generate architecture-specific serial evidence templates")
# @req: REQ-OS-BreaCounProbImag-001
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

- should generate parser-valid runtime serial evidence for staged probes
- Verify: should generate parser-valid runtime serial evidence for staged probes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate parser-valid runtime serial evidence for staged probes")
step("Verify: should generate parser-valid runtime serial evidence for staged probes")
# @req: REQ-OS-BreaCounProbImag-001
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

- should produce source contract text that records trap and evidence requirements
- Verify: should produce source contract text that records trap and evidence requirements


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should produce source contract text that records trap and evidence requirements")
step("Verify: should produce source contract text that records trap and evidence requirements")
# @req: REQ-OS-BreaCounProbImag-001
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

- should define original instruction bytes for native patch restore coverage
- Verify: should define original instruction bytes for native patch restore coverage
   - Expected: breakpoint_probe_original_instruction_bytes("x86_64") equals `90`
   - Expected: breakpoint_probe_original_instruction_bytes("thumb") equals `00 bf`
   - Expected: breakpoint_probe_original_instruction_bytes("aarch64") equals `1f 20 03 d5`
   - Expected: breakpoint_probe_original_instruction_bytes("riscv64c") equals `01 00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define original instruction bytes for native patch restore coverage")
step("Verify: should define original instruction bytes for native patch restore coverage")
# @req: REQ-OS-BreaCounProbImag-001
expect(breakpoint_probe_original_instruction_bytes("x86_64")).to_equal("90")
expect(breakpoint_probe_original_instruction_bytes("thumb")).to_equal("00 bf")
expect(breakpoint_probe_original_instruction_bytes("aarch64")).to_equal("1f 20 03 d5")
expect(breakpoint_probe_original_instruction_bytes("riscv64c")).to_equal("01 00")
```

</details>

#### should define architecture serial writes for QEMU serial output

- should define architecture serial writes for QEMU serial output
- Verify: should define architecture serial writes for QEMU serial output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define architecture serial writes for QEMU serial output")
step("Verify: should define architecture serial writes for QEMU serial output")
# @req: REQ-OS-BreaCounProbImag-001
expect(breakpoint_probe_serial_putc_body("x86_64")).to_contain("outb")
expect(breakpoint_probe_serial_putc_body("arm32")).to_contain("0x09000000")
expect(breakpoint_probe_serial_putc_body("aarch64")).to_contain("0x09000000")
expect(breakpoint_probe_serial_putc_body("riscv64c")).to_contain("0x10000000")
```

</details>

#### should define freestanding icache flushes without runtime library calls

- should define freestanding icache flushes without runtime library calls
- Verify: should define freestanding icache flushes without runtime library calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define freestanding icache flushes without runtime library calls")
step("Verify: should define freestanding icache flushes without runtime library calls")
# @req: REQ-OS-BreaCounProbImag-001
expect(breakpoint_probe_icache_flush_body("x86_64")).to_contain("memory")
expect(breakpoint_probe_icache_flush_body("arm32")).to_contain("dsb sy")
expect(breakpoint_probe_icache_flush_body("aarch64")).to_contain("isb")
expect(breakpoint_probe_icache_flush_body("riscv64c")).to_contain("fence.i")
```

</details>

#### should define boot entry shims for QEMU-loaded probes

- should define boot entry shims for QEMU-loaded probes
- Verify: should define boot entry shims for QEMU-loaded probes


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define boot entry shims for QEMU-loaded probes")
step("Verify: should define boot entry shims for QEMU-loaded probes")
# @req: REQ-OS-BreaCounProbImag-001
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

- should generate freestanding C that patches traps restores rearms and emits evidence
- Verify: should generate freestanding C that patches traps restores rearms and emits evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate freestanding C that patches traps restores rearms and emits evidence")
step("Verify: should generate freestanding C that patches traps restores rearms and emits evidence")
# @req: REQ-OS-BreaCounProbImag-001
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

- should package source artifacts with deterministic build locations
- Verify: should package source artifacts with deterministic build locations
   - Expected: artifact.valid is true
   - Expected: artifact.status equals `ready`
   - Expected: artifact.build_dir equals `build/baremetal/breakpoint_probe/thumb`
   - Expected: artifact.source_path equals `build/baremetal/breakpoint_probe/thumb/breakpoint_probe.c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should package source artifacts with deterministic build locations")
step("Verify: should package source artifacts with deterministic build locations")
# @req: REQ-OS-BreaCounProbImag-001
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

- should generate probe-specific linker scripts without full kernel symbols
- Verify: should generate probe-specific linker scripts without full kernel symbols
   - Expected: x86_linker does not contain `kernel__arch__x86_64`
   - Expected: artifact.valid is true
   - Expected: artifact.linker_script_path equals `build/baremetal/breakpoint_probe/riscv64c/breakpoint_probe.ld`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should generate probe-specific linker scripts without full kernel symbols")
step("Verify: should generate probe-specific linker scripts without full kernel symbols")
# @req: REQ-OS-BreaCounProbImag-001
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

- should package every supported architecture for staging
- Verify: should package every supported architecture for staging
   - Expected: artifacts.len() equals `9`
   - Expected: artifacts[0].source_path equals `build/baremetal/breakpoint_probe/i386/breakpoint_probe.c`
   - Expected: artifacts[8].source_path equals `build/baremetal/breakpoint_probe/riscv64c/breakpoint_probe.c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should package every supported architecture for staging")
step("Verify: should package every supported architecture for staging")
# @req: REQ-OS-BreaCounProbImag-001
val artifacts = breakpoint_probe_source_artifacts()
expect(artifacts.len()).to_equal(9)  # oracle: value fixed by the spec contract
expect(artifacts[0].source_path).to_equal("build/baremetal/breakpoint_probe/i386/breakpoint_probe.c")
expect(artifacts[8].source_path).to_equal("build/baremetal/breakpoint_probe/riscv64c/breakpoint_probe.c")
expect(artifacts[8].source_text).to_contain("hits=1")
```

</details>

#### should make all-arch staging idempotent

- should make all-arch staging idempotent
- Verify: should make all-arch staging idempotent
   - Expected: first.requested_count equals `9`
   - Expected: second.requested_count equals `9`
   - Expected: second.written_count equals `9`
   - Expected: second.failed_count equals `0`
   - Expected: second.status equals `written`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should make all-arch staging idempotent")
step("Verify: should make all-arch staging idempotent")
# @req: REQ-OS-BreaCounProbImag-001
val first = breakpoint_probe_stage_all_sources()
val second = breakpoint_probe_stage_all_sources()
expect(first.requested_count).to_equal(9)  # oracle: value fixed by the spec contract
expect(second.requested_count).to_equal(9)  # oracle: value fixed by the spec contract
expect(second.written_count).to_equal(9)  # oracle: value fixed by the spec contract
expect(second.failed_count).to_equal(0)  # oracle: value fixed by the spec contract
expect(second.status).to_equal("written")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-OS-BreaCounProbImag-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `38ffda6d6c63291a6fd38ec79d858a55c9a87e14870d1a49c8d08fa1d551ea9f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38ffda6d6c63291a6fd38ec79d858a55c9a87e14870d1a49c8d08fa1d551ea9f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38ffda6d6c63291a6fd38ec79d858a55c9a87e14870d1a49c8d08fa1d551ea9f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl
mirror: doc/06_spec/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should plan probe images for x86 ARM Thumb AArch64 and RISC-V compressed targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive deterministic source output linker compiler and serial driver paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should derive deterministic source output linker compiler and serial driver paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:82:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed until source compiler and ELF evidence are present' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed until source compiler and ELF evidence are present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should emit compiler arguments with the expected linker and output paths' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:135:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should require every field consumed by the QEMU evidence parser' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl:154:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate architecture-specific serial evidence templates' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
