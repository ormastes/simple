# SimpleOS Boot Smoke Tests

> Verifies each architecture can build and boot to serial output on QEMU. Tests target configuration, QEMU command generation, and architecture parsing.

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
| Updated | 2026-08-26 |
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

- has valid x86_64 target
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/x86_64/os_entry.spl`
   - Expected: target.linker_script equals `examples/09_embedded/simple_os/arch/x86_64/linker.ld`
   - Expected: target.target_triple equals `x86_64-unknown-none`
   - Expected: target.output equals `build/os/simpleos_x86_64.elf`
   - Expected: target.qemu_system equals `qemu-system-x86_64`
   - Expected: target.qemu_machine equals `q35`
   - Expected: target.qemu_cpu equals `qemu64`
   - Expected: target.qemu_memory equals `512M`
   - Expected: target.qemu_bios equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has valid x86_64 target")
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

- has valid x86_32 boot-probe target
   - Expected: target.entry equals `src/os/kernel/arch/x86_32/boot.spl`
   - Expected: target.linker_script equals `src/os/kernel/arch/x86_32/linker.ld`
   - Expected: target.target_triple equals `i686-unknown-none`
   - Expected: target.output equals `build/os/simpleos_x86_32.elf`
   - Expected: target.qemu_system equals `qemu-system-i386`
   - Expected: target.qemu_machine equals `pc`
   - Expected: target.qemu_cpu equals `qemu32`
   - Expected: target.qemu_memory equals `128M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has valid x86_32 boot-probe target")
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

- has valid riscv64 target
   - Expected: target.entry equals `src/os/kernel/arch/riscv64/boot.spl`
   - Expected: target.linker_script equals `src/os/kernel/arch/riscv64/linker.ld`
   - Expected: target.target_triple equals `riscv64-unknown-none`
   - Expected: target.output equals `build/os/simpleos_riscv64.elf`
   - Expected: target.qemu_system equals `qemu-system-riscv64`
   - Expected: target.qemu_machine equals `virt`
   - Expected: target.qemu_cpu equals `rv64`
   - Expected: target.qemu_bios equals `default`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has valid riscv64 target")
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

- has valid riscv32 target
   - Expected: target.entry equals `src/os/kernel/arch/riscv32/boot.spl`
   - Expected: target.linker_script equals `src/os/kernel/arch/riscv32/linker.ld`
   - Expected: target.target_triple equals `riscv32-unknown-none`
   - Expected: target.output equals `build/os/simpleos_riscv32.elf`
   - Expected: target.qemu_system equals `qemu-system-riscv32`
   - Expected: target.qemu_machine equals `virt`
   - Expected: target.qemu_cpu equals `rv32`
   - Expected: target.qemu_bios equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has valid riscv32 target")
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

- has valid arm64 target
   - Expected: target.entry equals `src/os/kernel/arch/arm64/boot.spl`
   - Expected: target.linker_script equals `src/os/kernel/arch/arm64/linker.ld`
   - Expected: target.target_triple equals `aarch64-unknown-none`
   - Expected: target.output equals `build/os/simpleos_aarch64.elf`
   - Expected: target.qemu_system equals `qemu-system-aarch64`
   - Expected: target.qemu_machine equals `virt`
   - Expected: target.qemu_cpu equals `cortex-a72`
   - Expected: target.qemu_bios equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has valid arm64 target")
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

- produces correct QEMU command for x86_64
   - Expected: cmd[0] equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces correct QEMU command for x86_64")
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

- produces correct QEMU command for x86_32 boot-probe target
   - Expected: target.qemu_system equals `qemu-system-i386`
   - Expected: cmd[0] equals `qemu-system-x86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces correct QEMU command for x86_32 boot-probe target")
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

- produces correct QEMU command for riscv64
   - Expected: cmd[0] equals `qemu-system-riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces correct QEMU command for riscv64")
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

- produces correct QEMU command for arm64
   - Expected: cmd[0] equals `qemu-system-aarch64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces correct QEMU command for arm64")
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

- parses x86_64
   - Expected: arch == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses x86_64")
val arch = arch_from_name("x86_64")
expect(arch == nil).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: parses x86_32 aliases</summary>

#### parses x86_32 aliases _(slow)_

- parses x86_32 aliases
   - Expected: x86_32 == nil is false
   - Expected: i686 == nil is false
   - Expected: i386 == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses x86_32 aliases")
val x86_32 = arch_from_name("x86_32")
expect(x86_32 == nil).to_equal(false)
val i686 = arch_from_name("i686")
expect(i686 == nil).to_equal(false)
val i386 = arch_from_name("i386")
expect(i386 == nil).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: parses riscv64</summary>

#### parses riscv64 _(slow)_

- parses riscv64
   - Expected: arch == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses riscv64")
val arch = arch_from_name("riscv64")
expect(arch == nil).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: parses riscv32</summary>

#### parses riscv32 _(slow)_

- parses riscv32
   - Expected: arch == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses riscv32")
val arch = arch_from_name("riscv32")
expect(arch == nil).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: parses arm64 and aarch64</summary>

#### parses arm64 and aarch64 _(slow)_

- parses arm64 and aarch64
   - Expected: arm == nil is false
   - Expected: aarch == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses arm64 and aarch64")
val arm = arch_from_name("arm64")
expect(arm == nil).to_equal(false)
val aarch = arch_from_name("aarch64")
expect(aarch == nil).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: returns nil for unknown architecture</summary>

#### returns nil for unknown architecture _(slow)_

- returns nil for unknown architecture
   - Expected: unknown == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns nil for unknown architecture")
val unknown = arch_from_name("mips")
expect(unknown == nil).to_equal(true)
```

</details>


</details>

### Target enumeration

<details>
<summary>Advanced: returns all supported targets</summary>

#### returns all supported targets _(slow)_

- returns all supported targets
   - Expected: targets.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns all supported targets")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SIMPLEOS-BOOT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c948c2058733f590588ecfea39e282561d30201b00986d30196141116955fd0c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c948c2058733f590588ecfea39e282561d30201b00986d30196141116955fd0c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c948c2058733f590588ecfea39e282561d30201b00986d30196141116955fd0c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/boot_smoke_spec.spl
mirror: doc/06_spec/03_system/os/boot_smoke_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=90
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/03_system/os/boot_smoke_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/boot_smoke_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/boot_smoke_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/boot_smoke_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/boot_smoke_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has valid x86_64 target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/boot_smoke_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has valid x86_32 boot-probe target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/boot_smoke_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has valid riscv64 target' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
