# Smf Enums Specification

> _Tests Platform enum u8 conversion, round-trip, and name methods._

<!-- sdn-diagram:id=smf_enums_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_enums_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_enums_spec -> compiler
smf_enums_spec -> std
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
expect(Platform.Any.to_u8()).to_equal(0)
expect(Platform.Linux.to_u8()).to_equal(1)
expect(Platform.Windows.to_u8()).to_equal(2)
expect(Platform.MacOS.to_u8()).to_equal(3)
expect(Platform.FreeBSD.to_u8()).to_equal(4)
expect(Platform.None_.to_u8()).to_equal(5)
```

</details>

#### defaults to Any for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.Any.to_u8()).to_equal(0)
```

</details>

#### converts Platform to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.Any.to_u8()).to_equal(0)
expect(Platform.Linux.to_u8()).to_equal(1)
expect(Platform.Windows.to_u8()).to_equal(2)
expect(Platform.MacOS.to_u8()).to_equal(3)
expect(Platform.FreeBSD.to_u8()).to_equal(4)
expect(Platform.None_.to_u8()).to_equal(5)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.Any.to_u8()).to_equal(0)
expect(Platform.Linux.to_u8()).to_equal(1)
expect(Platform.Windows.to_u8()).to_equal(2)
expect(Platform.MacOS.to_u8()).to_equal(3)
expect(Platform.FreeBSD.to_u8()).to_equal(4)
expect(Platform.None_.to_u8()).to_equal(5)
```

</details>

#### returns correct platform names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.Any.name()).to_equal("any")
expect(Platform.Linux.name()).to_equal("linux")
expect(Platform.Windows.name()).to_equal("windows")
expect(Platform.MacOS.name()).to_equal("macos")
expect(Platform.FreeBSD.name()).to_equal("freebsd")
expect(Platform.None_.name()).to_equal("none")
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
expect(Arch.X86_64.to_u8()).to_equal(0)
expect(Arch.Aarch64.to_u8()).to_equal(1)
expect(Arch.X86.to_u8()).to_equal(2)
expect(Arch.Arm.to_u8()).to_equal(3)
expect(Arch.Riscv64.to_u8()).to_equal(4)
expect(Arch.Riscv32.to_u8()).to_equal(5)
expect(Arch.Wasm32.to_u8()).to_equal(6)
expect(Arch.Wasm64.to_u8()).to_equal(7)
```

</details>

#### defaults to X86_64 for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.to_u8()).to_equal(0)
```

</details>

#### converts Arch to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.to_u8()).to_equal(0)
expect(Arch.Aarch64.to_u8()).to_equal(1)
expect(Arch.X86.to_u8()).to_equal(2)
expect(Arch.Arm.to_u8()).to_equal(3)
expect(Arch.Riscv64.to_u8()).to_equal(4)
expect(Arch.Riscv32.to_u8()).to_equal(5)
expect(Arch.Wasm32.to_u8()).to_equal(6)
expect(Arch.Wasm64.to_u8()).to_equal(7)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.to_u8()).to_equal(0)
expect(Arch.Aarch64.to_u8()).to_equal(1)
expect(Arch.X86.to_u8()).to_equal(2)
expect(Arch.Arm.to_u8()).to_equal(3)
expect(Arch.Riscv64.to_u8()).to_equal(4)
expect(Arch.Riscv32.to_u8()).to_equal(5)
expect(Arch.Wasm32.to_u8()).to_equal(6)
expect(Arch.Wasm64.to_u8()).to_equal(7)
```

</details>

#### returns correct architecture names

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.name()).to_equal("x86_64")
expect(Arch.Aarch64.name()).to_equal("aarch64")
expect(Arch.X86.name()).to_equal("x86")
expect(Arch.Arm.name()).to_equal("arm")
expect(Arch.Riscv64.name()).to_equal("riscv64")
expect(Arch.Riscv32.name()).to_equal("riscv32")
expect(Arch.Wasm32.name()).to_equal("wasm32")
expect(Arch.Wasm64.name()).to_equal("wasm64")
```

</details>

#### correctly identifies 32-bit architectures

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86.is_32bit()).to_equal(true)
expect(Arch.Arm.is_32bit()).to_equal(true)
expect(Arch.Riscv32.is_32bit()).to_equal(true)
expect(Arch.Wasm32.is_32bit()).to_equal(true)
expect(Arch.X86_64.is_32bit()).to_equal(false)
expect(Arch.Aarch64.is_32bit()).to_equal(false)
expect(Arch.Riscv64.is_32bit()).to_equal(false)
expect(Arch.Wasm64.is_32bit()).to_equal(false)
```

</details>

#### correctly identifies 64-bit architectures

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Arch.X86_64.is_64bit()).to_equal(true)
expect(Arch.Aarch64.is_64bit()).to_equal(true)
expect(Arch.Riscv64.is_64bit()).to_equal(true)
expect(Arch.Wasm64.is_64bit()).to_equal(true)
expect(Arch.X86.is_64bit()).to_equal(false)
expect(Arch.Arm.is_64bit()).to_equal(false)
expect(Arch.Riscv32.is_64bit()).to_equal(false)
expect(Arch.Wasm32.is_64bit()).to_equal(false)
```

</details>

### CompressionType enum

#### converts from u8 to CompressionType correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.None_.to_u8()).to_equal(0)
expect(CompressionType.Zstd.to_u8()).to_equal(1)
expect(CompressionType.Lz4.to_u8()).to_equal(2)
```

</details>

#### defaults to None_ for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.None_.to_u8()).to_equal(0)
```

</details>

#### converts CompressionType to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.None_.to_u8()).to_equal(0)
expect(CompressionType.Zstd.to_u8()).to_equal(1)
expect(CompressionType.Lz4.to_u8()).to_equal(2)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.None_.to_u8()).to_equal(0)
expect(CompressionType.Zstd.to_u8()).to_equal(1)
expect(CompressionType.Lz4.to_u8()).to_equal(2)
```

</details>

#### returns correct compression names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CompressionType.None_.name()).to_equal("none")
expect(CompressionType.Zstd.name()).to_equal("zstd")
expect(CompressionType.Lz4.name()).to_equal("lz4")
```

</details>

### SmfAppType enum

#### converts from u8 to SmfAppType correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.Cli.to_u8()).to_equal(0)
expect(SmfAppType.Tui.to_u8()).to_equal(1)
expect(SmfAppType.Gui.to_u8()).to_equal(2)
expect(SmfAppType.Service.to_u8()).to_equal(3)
expect(SmfAppType.Repl.to_u8()).to_equal(4)
```

</details>

#### defaults to Cli for unknown u8 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.Cli.to_u8()).to_equal(0)
```

</details>

#### converts SmfAppType to u8 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.Cli.to_u8()).to_equal(0)
expect(SmfAppType.Tui.to_u8()).to_equal(1)
expect(SmfAppType.Gui.to_u8()).to_equal(2)
expect(SmfAppType.Service.to_u8()).to_equal(3)
expect(SmfAppType.Repl.to_u8()).to_equal(4)
```

</details>

#### round-trips u8 conversion correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.Cli.to_u8()).to_equal(0)
expect(SmfAppType.Tui.to_u8()).to_equal(1)
expect(SmfAppType.Gui.to_u8()).to_equal(2)
expect(SmfAppType.Service.to_u8()).to_equal(3)
expect(SmfAppType.Repl.to_u8()).to_equal(4)
```

</details>

#### returns correct app type names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SmfAppType.Cli.name()).to_equal("cli")
expect(SmfAppType.Tui.name()).to_equal("tui")
expect(SmfAppType.Gui.name()).to_equal("gui")
expect(SmfAppType.Service.name()).to_equal("service")
expect(SmfAppType.Repl.name()).to_equal("repl")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_enums_spec.spl` |
| Updated | 2026-06-01 |
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
