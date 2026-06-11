# Smf Reader Specification

> <details>

<!-- sdn-diagram:id=smf_reader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_reader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_reader_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_reader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Reader Specification

## Scenarios

### Smf Reader

#### parses a raw header into the high-level header view

<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = SmfHeaderRaw(
    magic: [83, 77, 70, 0],
    version_major: 1,
    version_minor: 1,
    platform: 1,
    arch: 0,
    flags: 0x01 | 0x04 | 0x20,
    compression: 1,
    section_count: 4,
    section_table_offset: 128,
    symbol_table_offset: 256,
    symbol_count: 6,
    exported_count: 2,
    entry_point: 4096,
    stub_size: 0,
    smf_data_offset: 128,
    module_hash: 123,
    source_hash: 456,
    app_type: 0
)

val header = SmfHeader.from_raw(raw)
expect(header.version).to_equal((1, 1))
expect(header.platform).to_equal(Platform.Linux)
expect(header.arch).to_equal(Arch.X86_64)
expect(header.section_count).to_equal(4)
expect(header.symbol_count).to_equal(6)
expect(header.flags.executable).to_equal(true)
expect(header.flags.debug_info).to_equal(true)
expect(header.has_note_sdn).to_equal(true)
expect(header.compression).to_equal(CompressionType.Zstd)
expect(header.is_v1_1()).to_equal(true)
```

</details>

#### maps platform, arch, and compression helper values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_platform(1).name()).to_equal("linux")
expect(parse_platform(99).name()).to_equal("any")
expect(parse_arch(0).name()).to_equal("x86_64")
expect(parse_arch(7).name()).to_equal("wasm64")
expect(parse_compression(0).name()).to_equal("none")
expect(parse_compression(2).name()).to_equal("lz4")
```

</details>

#### parses bit flags consistently

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = parse_flags(0x01 | 0x02 | 0x08 | 0x10)
expect(flags.executable).to_equal(true)
expect(flags.reloadable).to_equal(true)
expect(flags.debug_info).to_equal(false)
expect(flags.pic).to_equal(true)
expect(flags.has_stub).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_reader_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Smf Reader

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
