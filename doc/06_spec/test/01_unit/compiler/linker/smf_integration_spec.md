# Smf Integration Specification

> 1. var header = SmfHeader new v1 1

<!-- sdn-diagram:id=smf_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_integration_spec -> compiler
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
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Integration Specification

## Scenarios

### Smf Integration

#### preserves key header fields through serialization

1. var header = SmfHeader new v1 1
2. header set executable
3. header set reloadable
4. header set compression
5. header set stub info
6. header set app type
7. header set window hints
8. header set prefetch hint
   - Expected: bytes.len() equals `SMF_HEADER_SIZE`
   - Expected: bytes[0] equals `83`
   - Expected: bytes[1] equals `77`
   - Expected: bytes[2] equals `70`
   - Expected: bytes[3] equals `0`
   - Expected: bytes[4] equals `1`
   - Expected: bytes[5] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
header.set_executable(true)
header.set_reloadable(true)
header.section_count = 5
header.symbol_count = 10
header.exported_count = 3
header.entry_point = 0x1000
header.set_compression(CompressionType.Zstd, 3)
header.set_stub_info(1024, 1024)
header.set_app_type(SmfAppType.Tui)
header.set_window_hints(1024, 768)
header.set_prefetch_hint(true, 8)

val bytes = header.to_bytes()
expect(bytes.len()).to_equal(SMF_HEADER_SIZE)
expect(bytes[0]).to_equal(83)
expect(bytes[1]).to_equal(77)
expect(bytes[2]).to_equal(70)
expect(bytes[3]).to_equal(0)
expect(bytes[4]).to_equal(1)
expect(bytes[5]).to_equal(1)
```

</details>

#### round-trips enum values through u8 conversions

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(Platform.Any.to_u8()).to_equal(0)
expect(Platform.Linux.to_u8()).to_equal(1)
expect(Platform.Windows.to_u8()).to_equal(2)
expect(Platform.MacOS.to_u8()).to_equal(3)
expect(Platform.FreeBSD.to_u8()).to_equal(4)
expect(Platform.None_.to_u8()).to_equal(5)

expect(Arch.X86_64.to_u8()).to_equal(0)
expect(Arch.Aarch64.to_u8()).to_equal(1)
expect(Arch.X86.to_u8()).to_equal(2)
expect(Arch.Arm.to_u8()).to_equal(3)
expect(Arch.Riscv64.to_u8()).to_equal(4)
expect(Arch.Riscv32.to_u8()).to_equal(5)
expect(Arch.Wasm32.to_u8()).to_equal(6)
expect(Arch.Wasm64.to_u8()).to_equal(7)

expect(CompressionType.None_.to_u8()).to_equal(0)
expect(CompressionType.Zstd.to_u8()).to_equal(1)
expect(CompressionType.Lz4.to_u8()).to_equal(2)

expect(SmfAppType.Cli.to_u8()).to_equal(0)
expect(SmfAppType.Tui.to_u8()).to_equal(1)
expect(SmfAppType.Gui.to_u8()).to_equal(2)
expect(SmfAppType.Service.to_u8()).to_equal(3)
expect(SmfAppType.Repl.to_u8()).to_equal(4)
```

</details>

#### builds minimal and full-featured headers

1. var full = SmfHeader new v1 1
2. full set executable
3. full set reloadable
4. full set debug info
5. full set pic
6. full set compression
7. full set stub info
8. full set app type
9. full set window hints
10. full set prefetch hint
   - Expected: full.to_bytes().len() equals `SMF_HEADER_SIZE`
   - Expected: full.is_executable() is true
   - Expected: full.is_reloadable() is true
   - Expected: full.has_debug_info() is true
   - Expected: full.is_pic() is true
   - Expected: full.is_compressed() is true
   - Expected: full.has_stub() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val minimal = SmfHeader.new_v1_1(Platform.Any, Arch.X86_64)
expect(minimal.to_bytes().len()).to_equal(SMF_HEADER_SIZE)
expect(minimal.is_executable()).to_equal(false)
expect(minimal.is_compressed()).to_equal(false)
expect(minimal.has_stub()).to_equal(false)

var full = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
full.set_executable(true)
full.set_reloadable(true)
full.set_debug_info(true)
full.set_pic(true)
full.set_compression(CompressionType.Zstd, 5)
full.set_stub_info(4096, 4096)
full.set_app_type(SmfAppType.Gui)
full.set_window_hints(1920, 1080)
full.set_prefetch_hint(true, 20)

expect(full.to_bytes().len()).to_equal(SMF_HEADER_SIZE)
expect(full.is_executable()).to_equal(true)
expect(full.is_reloadable()).to_equal(true)
expect(full.has_debug_info()).to_equal(true)
expect(full.is_pic()).to_equal(true)
expect(full.is_compressed()).to_equal(true)
expect(full.has_stub()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Smf Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
