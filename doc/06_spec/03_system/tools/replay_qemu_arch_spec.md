# Replay Qemu Arch Specification

> <details>

<!-- sdn-diagram:id=replay_qemu_arch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_qemu_arch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_qemu_arch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_qemu_arch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Qemu Arch Specification

## Scenarios

### Arch enum round-trip

#### riscv32 round-trips through from_text and to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Arch.from_text("riscv32")
expect(a.to_text()).to_equal("riscv32")
```

</details>

#### riscv64 round-trips through from_text and to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Arch.from_text("riscv64")
expect(a.to_text()).to_equal("riscv64")
```

</details>

#### x86_64 round-trips through from_text and to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Arch.from_text("x86_64")
expect(a.to_text()).to_equal("x86_64")
```

</details>

#### i386 alias resolves to X86_32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Arch.from_text("i386")
expect(a.to_text()).to_equal("x86_32")
```

</details>

#### aarch64 round-trips through from_text and to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = Arch.from_text("aarch64")
expect(a.to_text()).to_equal("aarch64")
```

</details>

### qemu_binary_for_arch

#### returns qemu-system-riscv32 for riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
```

</details>

#### returns qemu-system-riscv64 for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_binary_for_arch("riscv64")).to_equal("qemu-system-riscv64")
```

</details>

#### returns qemu-system-x86_64 for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_binary_for_arch("x86_64")).to_equal("qemu-system-x86_64")
```

</details>

#### returns qemu-system-i386 for i386

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_binary_for_arch("i386")).to_equal("qemu-system-i386")
```

</details>

#### returns qemu-system-aarch64 for aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_binary_for_arch("aarch64")).to_equal("qemu-system-aarch64")
```

</details>

### machine_for_arch

#### returns virt for riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(machine_for_arch("riscv32")).to_equal("virt")
```

</details>

#### returns virt for riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(machine_for_arch("riscv64")).to_equal("virt")
```

</details>

#### returns q35 for x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(machine_for_arch("x86_64")).to_equal("q35")
```

</details>

#### returns q35 for i386

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(machine_for_arch("i386")).to_equal("q35")
```

</details>

#### returns virt for aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(machine_for_arch("aarch64")).to_equal("virt")
```

</details>

### supported_architectures

#### returns exactly 5 entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archs = supported_architectures()
expect(archs.len()).to_equal(5)
```

</details>

#### contains riscv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archs = supported_architectures()
expect(archs).to_contain("riscv32")
```

</details>

#### contains riscv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archs = supported_architectures()
expect(archs).to_contain("riscv64")
```

</details>

#### contains x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archs = supported_architectures()
expect(archs).to_contain("x86_64")
```

</details>

#### contains i386

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archs = supported_architectures()
expect(archs).to_contain("i386")
```

</details>

#### contains aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archs = supported_architectures()
expect(archs).to_contain("aarch64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_qemu_arch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Arch enum round-trip
- qemu_binary_for_arch
- machine_for_arch
- supported_architectures

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
