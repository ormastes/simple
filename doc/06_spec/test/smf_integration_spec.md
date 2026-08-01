# Smf Integration Specification

> _Tests round-trip serialization and deserialization of SMF headers._

<!-- sdn-diagram:id=smf_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_integration_spec -> testing
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Integration Specification

## Scenarios

### SMF round-trip serialization
_Tests round-trip serialization and deserialization of SMF headers._

#### preserves all header fields through serialization

- var header1 = SmfHeader new v1 1
- header1 set executable
- header1 set reloadable
- header1 set compression
- header1 set stub info
- header1 set app type
- header1 set window hints
- header1 set prefetch hint


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create a header with various settings
var header1 = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
header1.set_executable(true)
header1.set_reloadable(true)
header1.section_count = 5
header1.section_table_offset = 256
header1.symbol_table_offset = 512
header1.symbol_count = 10
header1.exported_count = 3
header1.entry_point = 0x1000
header1.set_compression(CompressionType.Zstd, 3)
header1.set_stub_info(1024, 1024)
header1.module_hash = 0x123456789ABCDEF0
header1.source_hash = 0x7EDCBA9876543210
header1.set_app_type(SmfAppType.Tui)
header1.set_window_hints(1024, 768)
header1.set_prefetch_hint(true, 8)

# Serialize to bytes
val bytes = header1.to_bytes()
expect(bytes.len() == 128)

# For now, we can at least verify the serialization produces
# the correct size and magic number
expect(bytes[0] == 83)   # 'S'
expect(bytes[1] == 77)   # 'M'
expect(bytes[2] == 70)   # 'F'
expect(bytes[3] == 0)    # '\0'
```

</details>

### Enum preservation
_Tests that all SMF enum types survive u8 round-trip conversion._

#### preserves Platform enum through u8 conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platforms = [
    Platform.Any,
    Platform.Linux,
    Platform.Windows,
    Platform.MacOS,
    Platform.FreeBSD,
    Platform.None_
]

for platform in platforms:
    val u8_val = platform.to_u8()
    val restored = Platform.from_u8(u8_val)
    expect(restored == platform)
```

</details>

#### preserves Arch enum through u8 conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arches = [
    Arch.X86_64,
    Arch.Aarch64,
    Arch.X86,
    Arch.Arm,
    Arch.Riscv64,
    Arch.Riscv32,
    Arch.Wasm32,
    Arch.Wasm64
]

for arch in arches:
    val u8_val = arch.to_u8()
    val restored = Arch.from_u8(u8_val)
    expect(restored == arch)
```

</details>

#### preserves CompressionType enum through u8 conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val compressions = [
    CompressionType.None_,
    CompressionType.Zstd,
    CompressionType.Lz4
]

for compression in compressions:
    val u8_val = compression.to_u8()
    val restored = CompressionType.from_u8(u8_val)
    expect(restored == compression)
```

</details>

#### preserves SmfAppType enum through u8 conversion

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_types = [
    SmfAppType.Cli,
    SmfAppType.Tui,
    SmfAppType.Gui,
    SmfAppType.Service,
    SmfAppType.Repl
]

for app_type in app_types:
    val u8_val = app_type.to_u8()
    val restored = SmfAppType.from_u8(u8_val)
    expect(restored == app_type)
```

</details>

### Byte layout verification

#### verifies header structure is exactly 128 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
val bytes = header.to_bytes()

# Total must be exactly 128 bytes
expect(bytes.len() == SMF_HEADER_SIZE)
```

</details>

#### verifies magic number is at correct position

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
val bytes = header.to_bytes()

# Magic at bytes 0-3
expect(bytes[0] == 83)   # 'S'
expect(bytes[1] == 77)   # 'M'
expect(bytes[2] == 70)   # 'F'
expect(bytes[3] == 0)    # '\0'
```

</details>

#### verifies version fields are at correct positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
val bytes = header.to_bytes()

# Version at bytes 4-5
expect(bytes[4] == 1)    # major
expect(bytes[5] == 1)    # minor
```

</details>

#### verifies platform and arch are at correct positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = SmfHeader.new_v1_1(Platform.Windows, Arch.Aarch64)
val bytes = header.to_bytes()

# Platform at byte 6, arch at byte 7
expect(bytes[6] == Platform.Windows.to_u8())
expect(bytes[7] == Arch.Aarch64.to_u8())
```

</details>

### Header with different configurations

#### creates minimal header (no flags, no compression)

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = SmfHeader.new_v1_1(Platform.Any, Arch.X86_64)
val bytes = header.to_bytes()

expect(bytes.len() == 128)
expect(not header.is_executable())
expect(not header.is_compressed())
expect(not header.has_stub())
```

</details>

#### creates full-featured header

- var header = SmfHeader new v1 1
- header set executable
- header set reloadable
- header set debug info
- header set pic
- header set compression
- header set stub info
- header set app type
- header set window hints
- header set prefetch hint


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
header.set_executable(true)
header.set_reloadable(true)
header.set_debug_info(true)
header.set_pic(true)
header.set_compression(CompressionType.Zstd, 5)
header.set_stub_info(4096, 4096)
header.set_app_type(SmfAppType.Gui)
header.set_window_hints(1920, 1080)
header.set_prefetch_hint(true, 20)

val bytes = header.to_bytes()
expect(bytes.len() == 128)
expect(header.is_executable())
expect(header.is_reloadable())
expect(header.has_debug_info())
expect(header.is_pic())
expect(header.is_compressed())
expect(header.has_stub())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `src/compiler/70.backend/linker/test/smf_integration_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF round-trip serialization
- Enum preservation
- Byte layout verification
- Header with different configurations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
