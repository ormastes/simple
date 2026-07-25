# Path to the representative small SMF (same writer as compile.smf).

> use compiler.backend.linker.smf_reader_memory.{SmfReaderMemory}

<!-- sdn-diagram:id=simple_smf_format_validity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_smf_format_validity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_smf_format_validity_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_smf_format_validity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Path to the representative small SMF (same writer as compile.smf).

use compiler.backend.linker.smf_reader_memory.{SmfReaderMemory}

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/simple_smf_format_validity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

use compiler.backend.linker.smf_reader_memory.{SmfReaderMemory}

extern fn rt_file_read_bytes(path: text) -> [u8]
extern fn rt_file_exists(path: text) -> bool
extern fn rt_smf_relocs_from_path(path: text, sections_off: i64, section_count: i64, smf_data_offset: i64) -> [i64]

val SMALL_SMF_PATH = "build/mcp/t32_mcp.smf"

val COMPILER_SMF_PATH = "build/os/simple_cli_apps/x86_64/compile.smf"

describe "SMF format validity — baked Simple binaries":

## Scenarios

### SMF format validity — baked Simple binaries

#### baked SMF files exist on disk

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rt_file_exists(SMALL_SMF_PATH)).to_equal(true)
expect(rt_file_exists(COMPILER_SMF_PATH)).to_equal(true)
```

</details>

#### small SMF has correct magic bytes at offset 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(SMALL_SMF_PATH) ?? []
# Magic must be 'S' 'M' 'F' '\0'
expect(data.len() >= 4).to_equal(true)
expect(data[0]).to_equal(83)   # 'S'
expect(data[1]).to_equal(77)   # 'M'
expect(data[2]).to_equal(70)   # 'F'
expect(data[3]).to_equal(0)    # '\0'
```

</details>

#### small SMF is large enough to contain a full 128-byte header

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(SMALL_SMF_PATH) ?? []
expect(data.len() >= 128).to_equal(true)
```

</details>

#### small SMF parses successfully with SmfReaderMemory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(SMALL_SMF_PATH) ?? []
val result = SmfReaderMemory.from_data(data)
# This MUST return Ok — if it fails the SMF backend is broken
expect(result.is_ok()).to_equal(true)
```

</details>

#### small SMF header has version 1.1 (the contract version)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(SMALL_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
# Verify parse succeeded first — a failure here means the format is invalid
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
val (major, minor) = header.version
# v1.1 is the only version SmfReaderMemory and the SimpleOS loader support
expect(major).to_equal(1)
expect(minor).to_equal(1)
```

</details>

#### small SMF header has non-zero section count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(SMALL_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
expect(header.section_count > 0).to_equal(true)
```

</details>

#### small SMF has a sensible symbol count (>= 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(SMALL_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
expect(header.symbol_count >= 0).to_equal(true)
```

</details>

#### compiler SMF has correct magic bytes at offset 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(COMPILER_SMF_PATH) ?? []
expect(data.len() >= 4).to_equal(true)
expect(data[0]).to_equal(83)   # 'S'
expect(data[1]).to_equal(77)   # 'M'
expect(data[2]).to_equal(70)   # 'F'
expect(data[3]).to_equal(0)    # '\0'
```

</details>

#### compiler SMF parses successfully with SmfReaderMemory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(COMPILER_SMF_PATH) ?? []
val result = SmfReaderMemory.from_data(data)
# This MUST return Ok — if it fails the SMF backend is broken
expect(result.is_ok()).to_equal(true)
```

</details>

#### compiler SMF header has version 1.1

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(COMPILER_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
val (major, minor) = header.version
expect(major).to_equal(1)
expect(minor).to_equal(1)
```

</details>

#### compiler SMF has a positive section count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(COMPILER_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
expect(header.section_count > 0).to_equal(true)
```

</details>

#### compiler SMF has a sensible symbol count

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(COMPILER_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
# A compiler binary should have at least one symbol
expect(header.symbol_count > 0).to_equal(true)
```

</details>

#### compiler SMF relocation table is parseable

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use rt_smf_relocs_from_path (native Rust file read) to avoid passing
# 8.6MB [u8] through FFI (which causes >120s timeout in interpreter mode).
val data = rt_file_read_bytes(COMPILER_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
val sec_off = header.section_table_offset
val sec_cnt = header.section_count as i64
val data_off = header.smf_data_offset
val flat = rt_smf_relocs_from_path(COMPILER_SMF_PATH, sec_off, sec_cnt, data_off)
val flat_len = flat.len()
expect(flat_len >= 0).to_equal(true)
```

</details>

#### compiler SMF reloc count is sensible (< 10 million)

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = rt_file_read_bytes(COMPILER_SMF_PATH) ?? []
val parse_result = SmfReaderMemory.from_data(data)
expect(parse_result.is_ok()).to_equal(true)
val reader = parse_result.unwrap()
val header = reader.get_header()
val flat = rt_smf_relocs_from_path(
    COMPILER_SMF_PATH,
    header.section_table_offset,
    header.section_count as i64,
    header.smf_data_offset
)
# flat is [sym_idx, offset, addend, reloc_type, ...] 4 i64s per reloc
val reloc_count = flat.len() / 4
expect(reloc_count < 10000000).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
