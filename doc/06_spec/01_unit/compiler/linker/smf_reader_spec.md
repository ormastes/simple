# smf_reader_spec

> SMF reader specification tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_reader_spec

SMF reader specification tests.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_reader_spec.spl` |
| Updated | 2026-10-09 |
| Generator | `simple spipe-docgen` (Simple) |

SMF reader specification tests.

## Scenarios

### Smf Reader

#### parses a raw header into the high-level header view

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a raw header into the high-level header view
   - Expected: header.version equals `(1, 1)`
   - Expected: header.platform equals `Platform.Linux`
   - Expected: header.arch equals `Arch.X86_64`
   - Expected: header.section_count equals `4`
   - Expected: header.symbol_count equals `6`
   - Expected: header.flags.executable is true
   - Expected: header.flags.debug_info is true
   - Expected: header.has_note_sdn is true
   - Expected: header.compression equals `CompressionType.Zstd`
   - Expected: header.is_v1_1() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses a raw header into the high-level header view")
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

val header = SmfReaderHeader.from_raw(raw)
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

- maps platform, arch, and compression helper values
   - Expected: parse_platform(1).name() equals `linux`
   - Expected: parse_platform(99).name() equals `any`
   - Expected: parse_arch(0).name() equals `x86_64`
   - Expected: parse_arch(7).name() equals `wasm64`
   - Expected: parse_compression(0).name() equals `none`
   - Expected: parse_compression(2).name() equals `lz4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps platform, arch, and compression helper values")
expect(parse_platform(1).name()).to_equal("linux")
expect(parse_platform(99).name()).to_equal("any")
expect(parse_arch(0).name()).to_equal("x86_64")
expect(parse_arch(7).name()).to_equal("wasm64")
expect(parse_compression(0).name()).to_equal("none")
expect(parse_compression(2).name()).to_equal("lz4")
```

</details>

#### parses bit flags consistently

- parses bit flags consistently
   - Expected: flags.executable is true
   - Expected: flags.reloadable is true
   - Expected: flags.debug_info is false
   - Expected: flags.pic is true
   - Expected: flags.has_stub is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses bit flags consistently")
val flags = parse_flags(0x01 | 0x02 | 0x08 | 0x10)
expect(flags.executable).to_equal(true)
expect(flags.reloadable).to_equal(true)
expect(flags.debug_info).to_equal(false)
expect(flags.pic).to_equal(true)
expect(flags.has_stub).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
