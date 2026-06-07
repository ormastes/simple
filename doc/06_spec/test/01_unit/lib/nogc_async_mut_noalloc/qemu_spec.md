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
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Specification

## Scenarios

### Qemu

#### defines QEMU architectures and default command mappings

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qemu = rt_file_read_text("src/lib/nogc_async_mut_noalloc/qemu/mod.spl")

expect(qemu).to_contain("enum QemuArch:")
expect(qemu).to_contain("case QemuArch.X86: \"qemu-system-i386\"")
expect(qemu).to_contain("case QemuArch.X86_64: \"qemu-system-x86_64\"")
expect(qemu).to_contain("case QemuArch.ARM32: \"qemu-system-arm\"")
expect(qemu).to_contain("case QemuArch.ARM64: \"qemu-system-aarch64\"")
expect(qemu).to_contain("case QemuArch.RiscV32: \"qemu-system-riscv32\"")
expect(qemu).to_contain("case QemuArch.RiscV64: \"qemu-system-riscv64\"")
expect(qemu).to_contain("fn from_string(s: text) -> QemuArch:")
```

</details>

#### defines QEMU config, instance, exit-code, and availability contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qemu = rt_file_read_text("src/lib/nogc_async_mut_noalloc/qemu/mod.spl")
val init = rt_file_read_text("src/lib/nogc_async_mut_noalloc/qemu/__init__.spl")

expect(qemu).to_contain("class QemuConfig:")
expect(qemu).to_contain("static fn for_remote_debug(arch: QemuArch, elf_path: text, port: i32) -> QemuConfig:")
expect(qemu).to_contain("static fn for_test_runner(arch: QemuArch, elf_path: text) -> QemuConfig:")
expect(qemu).to_contain("fn build_args() -> [text]:")
expect(qemu).to_contain("class QemuInstance:")
expect(qemu).to_contain("static fn start(config: QemuConfig) -> Result<QemuInstance, text>:")
expect(qemu).to_contain("class ExitCodeResult:")
expect(qemu).to_contain("fn interpret_exit_code(exit_code: i32, has_debug_exit: bool) -> ExitCodeResult:")
expect(qemu).to_contain("fn is_qemu_available(arch: QemuArch) -> bool:")
expect(qemu).to_contain("fn find_gdb(arch: QemuArch) -> text:")
expect(init).to_contain("export run_boot_test, is_qemu_available, is_gdb_available")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Qemu

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
