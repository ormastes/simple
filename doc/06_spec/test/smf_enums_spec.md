# Smf Enums Specification

> _Tests Platform enum u8 conversion, round-trip, and name methods._

<!-- sdn-diagram:id=smf_enums_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_enums_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_enums_spec -> testing
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_enums_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Enums Specification

## Scenarios

### Platform enum
_Tests Platform enum u8 conversion, round-trip, and name methods._

#### converts from u8 to Platform correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.from_u8(0) == Platform.Any)
expect(Platform.from_u8(1) == Platform.Linux)
expect(Platform.from_u8(2) == Platform.Windows)
expect(Platform.from_u8(3) == Platform.MacOS)
expect(Platform.from_u8(4) == Platform.FreeBSD)
expect(Platform.from_u8(5) == Platform.None_)
```

</details>

#### defaults to Any for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.from_u8(99) == Platform.Any)
expect(Platform.from_u8(255) == Platform.Any)
```

</details>

#### converts Platform to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.Any.to_u8() == 0)
expect(Platform.Linux.to_u8() == 1)
expect(Platform.Windows.to_u8() == 2)
expect(Platform.MacOS.to_u8() == 3)
expect(Platform.FreeBSD.to_u8() == 4)
expect(Platform.None_.to_u8() == 5)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..6:
    val platform = Platform.from_u8(i)
    expect(platform.to_u8() == i)
```

</details>

#### returns correct platform names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.Any.name() == "any")
expect(Platform.Linux.name() == "linux")
expect(Platform.Windows.name() == "windows")
expect(Platform.MacOS.name() == "macos")
expect(Platform.FreeBSD.name() == "freebsd")
expect(Platform.None_.name() == "none")
```

</details>

### Arch enum
_Tests Arch enum u8 conversion, round-trip, bitness detection, and name methods._

#### converts from u8 to Arch correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.from_u8(0) == Arch.X86_64)
expect(Arch.from_u8(1) == Arch.Aarch64)
expect(Arch.from_u8(2) == Arch.X86)
expect(Arch.from_u8(3) == Arch.Arm)
expect(Arch.from_u8(4) == Arch.Riscv64)
expect(Arch.from_u8(5) == Arch.Riscv32)
expect(Arch.from_u8(6) == Arch.Wasm32)
expect(Arch.from_u8(7) == Arch.Wasm64)
```

</details>

#### defaults to X86_64 for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.from_u8(99) == Arch.X86_64)
expect(Arch.from_u8(255) == Arch.X86_64)
```

</details>

#### converts Arch to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.to_u8() == 0)
expect(Arch.Aarch64.to_u8() == 1)
expect(Arch.X86.to_u8() == 2)
expect(Arch.Arm.to_u8() == 3)
expect(Arch.Riscv64.to_u8() == 4)
expect(Arch.Riscv32.to_u8() == 5)
expect(Arch.Wasm32.to_u8() == 6)
expect(Arch.Wasm64.to_u8() == 7)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..8:
    val arch = Arch.from_u8(i)
    expect(arch.to_u8() == i)
```

</details>

#### returns correct architecture names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.name() == "x86_64")
expect(Arch.Aarch64.name() == "aarch64")
expect(Arch.X86.name() == "x86")
expect(Arch.Arm.name() == "arm")
expect(Arch.Riscv64.name() == "riscv64")
expect(Arch.Riscv32.name() == "riscv32")
expect(Arch.Wasm32.name() == "wasm32")
expect(Arch.Wasm64.name() == "wasm64")
```

</details>

#### correctly identifies 32-bit architectures

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86.is_32bit())
expect(Arch.Arm.is_32bit())
expect(Arch.Riscv32.is_32bit())
expect(Arch.Wasm32.is_32bit())

expect(not Arch.X86_64.is_32bit())
expect(not Arch.Aarch64.is_32bit())
expect(not Arch.Riscv64.is_32bit())
expect(not Arch.Wasm64.is_32bit())
```

</details>

#### correctly identifies 64-bit architectures

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.is_64bit())
expect(Arch.Aarch64.is_64bit())
expect(Arch.Riscv64.is_64bit())
expect(Arch.Wasm64.is_64bit())

expect(not Arch.X86.is_64bit())
expect(not Arch.Arm.is_64bit())
expect(not Arch.Riscv32.is_64bit())
expect(not Arch.Wasm32.is_64bit())
```

</details>

### CompressionType enum

#### converts from u8 to CompressionType correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.from_u8(0) == CompressionType.None_)
expect(CompressionType.from_u8(1) == CompressionType.Zstd)
expect(CompressionType.from_u8(2) == CompressionType.Lz4)
```

</details>

#### defaults to None_ for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.from_u8(99) == CompressionType.None_)
expect(CompressionType.from_u8(255) == CompressionType.None_)
```

</details>

#### converts CompressionType to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.None_.to_u8() == 0)
expect(CompressionType.Zstd.to_u8() == 1)
expect(CompressionType.Lz4.to_u8() == 2)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..3:
    val compression = CompressionType.from_u8(i)
    expect(compression.to_u8() == i)
```

</details>

#### returns correct compression names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.None_.name() == "none")
expect(CompressionType.Zstd.name() == "zstd")
expect(CompressionType.Lz4.name() == "lz4")
```

</details>

### SmfAppType enum

#### converts from u8 to SmfAppType correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.from_u8(0) == SmfAppType.Cli)
expect(SmfAppType.from_u8(1) == SmfAppType.Tui)
expect(SmfAppType.from_u8(2) == SmfAppType.Gui)
expect(SmfAppType.from_u8(3) == SmfAppType.Service)
expect(SmfAppType.from_u8(4) == SmfAppType.Repl)
```

</details>

#### defaults to Cli for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.from_u8(99) == SmfAppType.Cli)
expect(SmfAppType.from_u8(255) == SmfAppType.Cli)
```

</details>

#### converts SmfAppType to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.Cli.to_u8() == 0)
expect(SmfAppType.Tui.to_u8() == 1)
expect(SmfAppType.Gui.to_u8() == 2)
expect(SmfAppType.Service.to_u8() == 3)
expect(SmfAppType.Repl.to_u8() == 4)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for i in 0..5:
    val app_type = SmfAppType.from_u8(i)
    expect(app_type.to_u8() == i)
```

</details>

#### returns correct app type names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.Cli.name() == "cli")
expect(SmfAppType.Tui.name() == "tui")
expect(SmfAppType.Gui.name() == "gui")
expect(SmfAppType.Service.name() == "service")
expect(SmfAppType.Repl.name() == "repl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `src/compiler/70.backend/linker/test/smf_enums_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Platform enum
- Arch enum
- CompressionType enum
- SmfAppType enum

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
