# Qemu Specification

> <details>

<!-- sdn-diagram:id=qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Specification

## Scenarios

### Qemu

#### should define supported QEMU architectures and command names

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = qemu_source()
expect(src.contains("enum QemuArch")).to_equal(true)
expect(src.contains("case QemuArch.X86: \"qemu-system-i386\"")).to_equal(true)
expect(src.contains("case QemuArch.X86_64: \"qemu-system-x86_64\"")).to_equal(true)
expect(src.contains("case QemuArch.ARM64: \"qemu-system-aarch64\"")).to_equal(true)
expect(src.contains("case QemuArch.RiscV32: \"qemu-system-riscv32\"")).to_equal(true)
expect(src.contains("case QemuArch.RiscV64: \"qemu-system-riscv64\"")).to_equal(true)
```

</details>

#### should define architecture defaults and aliases

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = qemu_source()
expect(src.contains("fn default_machine() -> text")).to_equal(true)
expect(src.contains("case QemuArch.ARM32: \"lm3s6965evb\"")).to_equal(true)
expect(src.contains("fn default_memory() -> text")).to_equal(true)
expect(src.contains("case QemuArch.ARM32: \"16M\"")).to_equal(true)
expect(src.contains("fn from_string(s: text) -> QemuArch")).to_equal(true)
expect(src.contains("elif s == \"riscv64\" or s == \"rv64\"")).to_equal(true)
```

</details>

#### should define remote debug and test runner configurations

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = qemu_source()
expect(src.contains("class QemuConfig")).to_equal(true)
expect(src.contains("static fn for_remote_debug(arch: QemuArch, elf_path: text, port: i32) -> QemuConfig")).to_equal(true)
expect(src.contains("gdb_enabled: true")).to_equal(true)
expect(src.contains("gdb_wait: true")).to_equal(true)
expect(src.contains("static fn for_test_runner(arch: QemuArch, elf_path: text) -> QemuConfig")).to_equal(true)
expect(src.contains("serial_stdio: true")).to_equal(true)
expect(src.contains("debug_exit: true")).to_equal(true)
```

</details>

#### should build QEMU command line arguments from config fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = qemu_source()
expect(src.contains("fn build_args() -> [text]")).to_equal(true)
expect(src.contains("args.push(\"-machine\")")).to_equal(true)
expect(src.contains("args.push(\"-kernel\")")).to_equal(true)
expect(src.contains("args.push(\"-gdb\")")).to_equal(true)
expect(src.contains("args.push(\"-serial\")")).to_equal(true)
expect(src.contains("isa-debug-exit,iobase=0xf4,iosize=0x04")).to_equal(true)
```

</details>

#### should expose process launch exit interpretation and tool discovery

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = qemu_source()
expect(src.contains("class QemuInstance")).to_equal(true)
expect(src.contains("static fn start(config: QemuConfig) -> Result<QemuInstance, text>")).to_equal(true)
expect(src.contains("fn interpret_exit_code(exit_code: i32, has_debug_exit: bool) -> ExitCodeResult")).to_equal(true)
expect(src.contains("fn is_qemu_available(arch: QemuArch) -> bool")).to_equal(true)
expect(src.contains("fn find_gdb(arch: QemuArch) -> text")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Qemu

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
