# Replay Qemu E2e Specification

> <details>

<!-- sdn-diagram:id=replay_qemu_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_qemu_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_qemu_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_qemu_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Qemu E2e Specification

## Scenarios

### SReplay QEMU E2E — mock level

### ReplayConfig record mode

#### arch field matches requested arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_record_arch()).to_equal("x86_64")
```

</details>

#### mode field is record

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_record_mode()).to_equal("record")
```

</details>

#### kernel_path field is preserved

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_record_kernel()).to_equal("/boot/vmlinux")
```

</details>

### ReplayConfig replay mode

#### mode field is replay

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_replay_mode()).to_equal("replay")
```

</details>

#### gdb_port defaults to 1234

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_replay_gdb_port()).to_equal(1234)
```

</details>

### Arch.from_text

#### parses x86_32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_from_text_x86_32()).to_equal("x86_32")
```

</details>

#### parses x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_from_text_x86_64()).to_equal("x86_64")
```

</details>

#### parses arm32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_from_text_arm32()).to_equal("arm32")
```

</details>

#### parses aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_from_text_aarch64()).to_equal("aarch64")
```

</details>

#### parses riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_from_text_riscv32()).to_equal("riscv32")
```

</details>

#### parses riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_from_text_riscv64()).to_equal("riscv64")
```

</details>

### Arch.qemu_system_cmd

#### x86_32 → qemu-system-i386

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qemu_cmd_x86_32()).to_equal("qemu-system-i386")
```

</details>

#### x86_64 → qemu-system-x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qemu_cmd_x86_64()).to_equal("qemu-system-x86_64")
```

</details>

#### arm32 → qemu-system-arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qemu_cmd_arm32()).to_equal("qemu-system-arm")
```

</details>

#### aarch64 → qemu-system-aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qemu_cmd_aarch64()).to_equal("qemu-system-aarch64")
```

</details>

#### riscv32 → qemu-system-riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qemu_cmd_riscv32()).to_equal("qemu-system-riscv32")
```

</details>

#### riscv64 → qemu-system-riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_qemu_cmd_riscv64()).to_equal("qemu-system-riscv64")
```

</details>

### Arch.default_machine

#### x86_32 → q35

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_machine_x86_32()).to_equal("q35")
```

</details>

#### x86_64 → q35

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_machine_x86_64()).to_equal("q35")
```

</details>

#### arm32 → virt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_machine_arm32()).to_equal("virt")
```

</details>

#### aarch64 → virt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_machine_aarch64()).to_equal("virt")
```

</details>

#### riscv32 → virt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_machine_riscv32()).to_equal("virt")
```

</details>

#### riscv64 → virt

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_machine_riscv64()).to_equal("virt")
```

</details>

### Arch.pointer_bits

#### x86_32 is 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bits_x86_32()).to_equal(32)
```

</details>

#### x86_64 is 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bits_x86_64()).to_equal(64)
```

</details>

#### arm32 is 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bits_arm32()).to_equal(32)
```

</details>

#### aarch64 is 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bits_aarch64()).to_equal(64)
```

</details>

#### riscv32 is 32-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bits_riscv32()).to_equal(32)
```

</details>

#### riscv64 is 64-bit

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_bits_riscv64()).to_equal(64)
```

</details>

### TargetDesc.for_arch

#### arch field matches requested arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_target_arch()).to_equal("riscv64")
```

</details>

#### page_size is 4096

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_target_page_size()).to_equal(4096)
```

</details>

#### x86_64 register schema is x86_64-sysv-v1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_target_schema_x86_64()).to_equal("x86_64-sysv-v1")
```

</details>

#### aarch64 register schema is aarch64-v1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_target_schema_aarch64()).to_equal("aarch64-v1")
```

</details>

#### x86_64 endian is little

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_target_endian_x86_64()).to_equal("little")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_qemu_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SReplay QEMU E2E — mock level
- ReplayConfig record mode
- ReplayConfig replay mode
- Arch.from_text
- Arch.qemu_system_cmd
- Arch.default_machine
- Arch.pointer_bits
- TargetDesc.for_arch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
