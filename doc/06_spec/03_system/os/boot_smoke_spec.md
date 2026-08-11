# SimpleOS Boot Smoke Tests

> Verifies each architecture can build and boot to serial output on QEMU. Tests target configuration, QEMU command generation, and architecture parsing.

<!-- sdn-diagram:id=boot_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=boot_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

boot_smoke_spec -> std
boot_smoke_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=boot_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Boot Smoke Tests

Verifies each architecture can build and boot to serial output on QEMU. Tests target configuration, QEMU command generation, and architecture parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-BOOT-001 |
| Category | Operating System |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/03_system/os/boot_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies each architecture can build and boot to serial output on QEMU.
Tests target configuration, QEMU command generation, and architecture parsing.

## Prerequisites

QEMU must be installed for each architecture:
  apt install qemu-system-x86 qemu-system-arm qemu-system-misc

## Scenarios

### OS build configuration

<details>
<summary>Advanced: has valid x86_64 target</summary>

#### has valid x86_64 target _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.X86_64)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/os_entry.spl")
expect(target.linker_script).to_equal("examples/09_embedded/simple_os/arch/x86_64/linker.ld")
expect(target.target_triple).to_equal("x86_64-unknown-none")
expect(target.output).to_equal("build/os/simpleos_x86_64.elf")
expect(target.qemu_system).to_equal("qemu-system-x86_64")
expect(target.qemu_machine).to_equal("q35")
expect(target.qemu_cpu).to_equal("qemu64")
expect(target.qemu_memory).to_equal("512M")
expect(target.qemu_bios).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: has valid x86_32 boot-probe target</summary>

#### has valid x86_32 boot-probe target _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.X86)
expect(target.entry).to_equal("src/os/kernel/arch/x86_32/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/x86_32/linker.ld")
expect(target.target_triple).to_equal("i686-unknown-none")
expect(target.output).to_equal("build/os/simpleos_x86_32.elf")
expect(target.qemu_system).to_equal("qemu-system-i386")
expect(target.qemu_machine).to_equal("pc")
expect(target.qemu_cpu).to_equal("qemu32")
expect(target.qemu_memory).to_equal("128M")
```

</details>


</details>

<details>
<summary>Advanced: has valid riscv64 target</summary>

#### has valid riscv64 target _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.Riscv64)
expect(target.entry).to_equal("src/os/kernel/arch/riscv64/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/riscv64/linker.ld")
expect(target.target_triple).to_equal("riscv64-unknown-none")
expect(target.output).to_equal("build/os/simpleos_riscv64.elf")
expect(target.qemu_system).to_equal("qemu-system-riscv64")
expect(target.qemu_machine).to_equal("virt")
expect(target.qemu_cpu).to_equal("rv64")
expect(target.qemu_bios).to_equal("default")
```

</details>


</details>

<details>
<summary>Advanced: has valid riscv32 target</summary>

#### has valid riscv32 target _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.Riscv32)
expect(target.entry).to_equal("src/os/kernel/arch/riscv32/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/riscv32/linker.ld")
expect(target.target_triple).to_equal("riscv32-unknown-none")
expect(target.output).to_equal("build/os/simpleos_riscv32.elf")
expect(target.qemu_system).to_equal("qemu-system-riscv32")
expect(target.qemu_machine).to_equal("virt")
expect(target.qemu_cpu).to_equal("rv32")
expect(target.qemu_bios).to_equal("none")
```

</details>


</details>

<details>
<summary>Advanced: has valid arm64 target</summary>

#### has valid arm64 target _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.Arm64)
expect(target.entry).to_equal("src/os/kernel/arch/arm64/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/arm64/linker.ld")
expect(target.target_triple).to_equal("aarch64-unknown-none")
expect(target.output).to_equal("build/os/simpleos_aarch64.elf")
expect(target.qemu_system).to_equal("qemu-system-aarch64")
expect(target.qemu_machine).to_equal("virt")
expect(target.qemu_cpu).to_equal("cortex-a72")
expect(target.qemu_bios).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: produces correct QEMU command for x86_64</summary>

#### produces correct QEMU command for x86_64 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.X86_64)
val cmd = build_qemu_command(target)
expect(cmd[0]).to_equal("qemu-system-x86_64")
expect(cmd).to_contain("-machine")
expect(cmd).to_contain("q35")
expect(cmd).to_contain("-cpu")
expect(cmd).to_contain("qemu64")
expect(cmd).to_contain("-m")
expect(cmd).to_contain("512M")
expect(cmd).to_contain("-serial")
expect(cmd).to_contain("stdio")
expect(cmd).to_contain("-display")
expect(cmd).to_contain("none")
expect(cmd).to_contain("-no-reboot")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_x86_64.elf")
# x86_64 has debug-exit device
expect(cmd).to_contain("-device")
expect(cmd).to_contain("isa-debug-exit,iobase=0xf4,iosize=0x04")
```

</details>


</details>

<details>
<summary>Advanced: produces correct QEMU command for x86_32 boot-probe target</summary>

#### produces correct QEMU command for x86_32 boot-probe target _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.X86)
val cmd = build_qemu_command(target)
expect(target.qemu_system).to_equal("qemu-system-i386")
expect(cmd[0]).to_equal("qemu-system-x86_64")
expect(cmd).to_contain("-machine")
expect(cmd).to_contain("pc")
expect(cmd).to_contain("-cpu")
expect(cmd).to_contain("qemu32")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_x86_32.elf")
expect(cmd).to_contain("-device")
expect(cmd).to_contain("isa-debug-exit,iobase=0xf4,iosize=0x04")
```

</details>


</details>

<details>
<summary>Advanced: produces correct QEMU command for riscv64</summary>

#### produces correct QEMU command for riscv64 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.Riscv64)
val cmd = build_qemu_command(target)
expect(cmd[0]).to_equal("qemu-system-riscv64")
expect(cmd).to_contain("virt")
expect(cmd).to_contain("rv64")
expect(cmd).to_contain("-bios")
expect(cmd).to_contain("default")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_riscv64.elf")
```

</details>


</details>

<details>
<summary>Advanced: produces correct QEMU command for arm64</summary>

#### produces correct QEMU command for arm64 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = get_target(Architecture.Arm64)
val cmd = build_qemu_command(target)
expect(cmd[0]).to_equal("qemu-system-aarch64")
expect(cmd).to_contain("virt")
expect(cmd).to_contain("cortex-a72")
expect(cmd).to_contain("-kernel")
expect(cmd).to_contain("build/os/simpleos_aarch64.elf")
```

</details>


</details>

### Architecture name parsing

<details>
<summary>Advanced: parses x86_64</summary>

#### parses x86_64 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = arch_from_name("x86_64")
expect(arch.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses x86_32 aliases</summary>

#### parses x86_32 aliases _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86_32 = arch_from_name("x86_32")
expect(x86_32.?).to_equal(true)
val i686 = arch_from_name("i686")
expect(i686.?).to_equal(true)
val i386 = arch_from_name("i386")
expect(i386.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses riscv64</summary>

#### parses riscv64 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = arch_from_name("riscv64")
expect(arch.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses riscv32</summary>

#### parses riscv32 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = arch_from_name("riscv32")
expect(arch.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: parses arm64 and aarch64</summary>

#### parses arm64 and aarch64 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm = arch_from_name("arm64")
expect(arm.?).to_equal(true)
val aarch = arch_from_name("aarch64")
expect(aarch.?).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: returns nil for unknown architecture</summary>

#### returns nil for unknown architecture _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unknown = arch_from_name("mips")
expect(unknown.?).to_equal(false)
```

</details>


</details>

### Target enumeration

<details>
<summary>Advanced: returns all supported targets</summary>

#### returns all supported targets _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val targets = get_all_targets()
expect(targets.len()).to_equal(6)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 16 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
