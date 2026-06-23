# Breakpoint Counter Target Adapter Specification

> <details>

<!-- sdn-diagram:id=breakpoint_counter_target_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakpoint_counter_target_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakpoint_counter_target_adapter_spec -> std
breakpoint_counter_target_adapter_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakpoint_counter_target_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakpoint Counter Target Adapter Specification

## Scenarios

### Bare-metal Breakpoint Target Adapter Contract

### x86 trap frame normalization

#### should normalize x86 and x86_64 INT3 reported PCs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = breakpoint_x86_resume_plan("i386", 4097)
expect(x86.valid).to_equal(true)
expect(x86.patched_address).to_equal(4096)
expect(x86.restore_pc).to_equal(4096)
expect(x86.resume_pc_after_single_step).to_equal(4097)
expect(x86.trap_width_bytes).to_equal(1)
expect(breakpoint_x86_qemu_target("i386")).to_equal("qemu-system-i386")
expect(breakpoint_x86_qemu_target("x86_64")).to_equal("qemu-system-x86_64")
```

</details>

### ARM and Thumb trap frame normalization

#### should normalize ARM32, Thumb, and AArch64 resume PCs

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = breakpoint_arm_resume_plan("arm32", 8192)
expect(arm.valid).to_equal(true)
expect(arm.restore_pc).to_equal(8192)
expect(arm.resume_pc_after_single_step).to_equal(8196)
expect(arm.patch_width_bytes).to_equal(4)
expect(arm.requires_icache_flush).to_equal(true)

val thumb = breakpoint_arm_resume_plan("thumb", 8200)
expect(thumb.valid).to_equal(true)
expect(thumb.resume_pc_after_single_step).to_equal(8202)
expect(thumb.patch_width_bytes).to_equal(2)

val arm64 = breakpoint_arm_resume_plan("aarch64", 12288)
expect(arm64.valid).to_equal(true)
expect(arm64.resume_pc_after_single_step).to_equal(12292)
expect(breakpoint_arm_qemu_target("aarch64")).to_equal("qemu-system-aarch64")
```

</details>

### RISC-V trap frame normalization

#### should normalize RV32 RV64 and compressed RVC resume PCs

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv32 = breakpoint_riscv_resume_plan("riscv32", 16384)
expect(rv32.valid).to_equal(true)
expect(rv32.restore_pc).to_equal(16384)
expect(rv32.resume_pc_after_single_step).to_equal(16388)
expect(rv32.patch_width_bytes).to_equal(4)
expect(rv32.requires_fence_i).to_equal(true)
expect(rv32.compressed).to_equal(false)

val rvc = breakpoint_riscv_resume_plan("riscv64c", 16400)
expect(rvc.valid).to_equal(true)
expect(rvc.resume_pc_after_single_step).to_equal(16402)
expect(rvc.patch_width_bytes).to_equal(2)
expect(rvc.compressed).to_equal(true)
expect(breakpoint_riscv_qemu_target("riscv64c")).to_equal("qemu-system-riscv64")
```

</details>

### QEMU evidence normalization

#### should build fail-closed QEMU runner plans for supported target families

<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = breakpoint_qemu_runner_plan("x86_64", "build/bp-x86.elf", true, true)
expect(x86.can_run).to_equal(true)
expect(x86.qemu_binary).to_equal("qemu-system-x86_64")
expect(x86.machine).to_equal("pc")
expect(x86.args).to_contain("-kernel")
expect(x86.args).to_contain("build/bp-x86.elf")

val thumb = breakpoint_qemu_runner_plan("thumb", "build/bp-thumb.elf", true, true)
expect(thumb.can_run).to_equal(true)
expect(thumb.qemu_binary).to_equal("qemu-system-arm")
expect(thumb.machine).to_equal("virt")
expect(thumb.cpu).to_equal("cortex-a15")

val rvc = breakpoint_qemu_runner_plan("riscv64c", "build/bp-rvc.elf", true, true)
expect(rvc.can_run).to_equal(true)
expect(rvc.qemu_binary).to_equal("qemu-system-riscv64")
expect(rvc.machine).to_equal("virt")
expect(breakpoint_qemu_runner_plan("riscv32c", "build/bp-rv32c.elf", true, true).cpu).to_equal("rv32")

val missing_image = breakpoint_qemu_runner_plan("aarch64", "", true, false)
expect(missing_image.can_run).to_equal(false)
expect(missing_image.status).to_equal("missing_image")

val missing_qemu = breakpoint_qemu_runner_plan("riscv32", "build/bp-rv32.elf", false, true)
expect(missing_qemu.can_run).to_equal(false)
expect(missing_qemu.status).to_equal("qemu_unavailable")

val unsupported = breakpoint_qemu_runner_plan("mips64", "build/bp-mips.elf", true, true)
expect(unsupported.can_run).to_equal(false)
expect(unsupported.status).to_equal("unsupported_arch")
```

</details>

#### should expose deterministic QEMU command fragments for runner integration

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(breakpoint_qemu_binary_for_arch("i386")).to_equal("qemu-system-i386")
expect(breakpoint_qemu_binary_for_arch("aarch64")).to_equal("qemu-system-aarch64")
expect(breakpoint_qemu_binary_for_arch("riscv32c")).to_equal("qemu-system-riscv32")
expect(breakpoint_qemu_command_args("aarch64", "build/bp-aarch64.elf")).to_contain("cortex-a57")
expect(breakpoint_qemu_machine_for_arch("riscv64")).to_equal("virt")
val rv32_args = breakpoint_qemu_command_args("riscv32c", "build/bp-rv32c.elf")
expect(rv32_args).to_contain("-bios")
expect(rv32_args).to_contain("none")

val args = breakpoint_qemu_command_args("riscv64c", "build/bp-rvc.elf")
expect(args).to_contain("-M")
expect(args).to_contain("virt")
expect(args).to_contain("-monitor")
expect(args).to_contain("none")
expect(args).to_contain("-serial")
expect(args).to_contain("stdio")
expect(args).to_contain("-kernel")
expect(args).to_contain("build/bp-rvc.elf")
```

</details>

#### should accept complete target-backed evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = breakpoint_qemu_evidence_from_line(
    "arch=riscv64c;qemu=qemu-system-riscv64;address=16400;original=02 90;trap=02 90;hits=2;latency_us=40;restored=true;rearmed=true;cleanup=true;icache=true;sampled=none"
)
expect(evidence.valid).to_equal(true)
expect(evidence.arch).to_equal("riscv64c")
expect(evidence.hit_count).to_equal(2)
expect(evidence.status).to_equal("valid")

val thumb = breakpoint_qemu_evidence_from_line(
    "arch=thumb;qemu=qemu-system-arm;address=1048576;original=00 bf;trap=00 be;hits=1;latency_us=1;restored=true;rearmed=true;cleanup=true;icache=true;sampled=none"
)
expect(thumb.valid).to_equal(true)
expect(thumb.status).to_equal("valid")

val arm64 = breakpoint_qemu_evidence_from_line(
    "arch=aarch64;qemu=qemu-system-aarch64;address=1048576;original=1f 20 03 d5;trap=00 00 20 d4;hits=1;latency_us=1;restored=true;rearmed=true;cleanup=true;icache=true;sampled=none"
)
expect(arm64.valid).to_equal(true)
expect(arm64.status).to_equal("valid")
```

</details>

#### should fail closed for missing target evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_icache = breakpoint_qemu_evidence_from_line(
    "arch=aarch64;qemu=qemu-system-aarch64;address=12288;original=1f 20 03 d5;trap=00 00 20 d4;hits=1;latency_us=60;restored=true;rearmed=true;cleanup=true;icache=false;sampled=none"
)
expect(missing_icache.valid).to_equal(false)
expect(missing_icache.status).to_equal("missing_icache_flush")

val wrong_trap = breakpoint_qemu_evidence_from_line(
    "arch=x86_64;qemu=qemu-system-x86_64;address=4096;original=90;trap=00;hits=1;latency_us=10;restored=true;rearmed=true;cleanup=true;icache=false;sampled=none"
)
expect(wrong_trap.valid).to_equal(false)
expect(wrong_trap.status).to_equal("trap_bytes_mismatch")
```

</details>

#### should parse serial runner evidence lines without accepting missing proof

1. breakpoint qemu evidence prefix
2. ] join
   - Expected: evidence.valid is true
   - Expected: evidence.status equals `valid`
   - Expected: missing.valid is false
   - Expected: missing.status equals `missing_serial_evidence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial = [
    "booting",
    breakpoint_qemu_evidence_prefix() + "arch=x86_64;qemu=qemu-system-x86_64;address=4096;original=90;trap=cc;hits=1;latency_us=8;restored=true;rearmed=true;cleanup=true;icache=false;sampled=none",
    "halted"
].join("\n")
val line = breakpoint_qemu_serial_evidence_line(serial)
expect(line).to_contain("arch=x86_64")
val evidence = breakpoint_qemu_evidence_from_serial(serial)
expect(evidence.valid).to_equal(true)
expect(evidence.status).to_equal("valid")

val missing = breakpoint_qemu_evidence_from_serial("booting\nhalted\n")
expect(missing.valid).to_equal(false)
expect(missing.status).to_equal("missing_serial_evidence")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/os/baremetal/feature/breakpoint_counter_target_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Bare-metal Breakpoint Target Adapter Contract
- x86 trap frame normalization
- ARM and Thumb trap frame normalization
- RISC-V trap frame normalization
- QEMU evidence normalization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
