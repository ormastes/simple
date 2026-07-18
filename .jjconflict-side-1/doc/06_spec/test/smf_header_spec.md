# smf_header_spec

> Validates SMF header format functionality.

<!-- sdn-diagram:id=smf_header_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_header_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_header_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_header_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_header_spec

Validates SMF header format functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `src/compiler/70.backend/linker/test/smf_header_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Basic Tests

    Validates SMF header format functionality.

## Scenarios

### Smf Header

#### creates a v1.1 header with defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)

expect(header.version_major).to_equal(1)
expect(header.version_minor).to_equal(1)
expect(header.get_platform()).to_equal(Platform.Linux)
expect(header.get_arch()).to_equal(Arch.X86_64)
expect(header.flags).to_equal(0)
expect(header.window_width).to_equal(1280)
expect(header.window_height).to_equal(720)
```

</details>

#### updates flags independently

- var header = SmfHeader new v1 1
- header set executable
- header set reloadable
- header set debug info
- header set pic
   - Expected: header.is_executable() is true
   - Expected: header.is_reloadable() is true
   - Expected: header.has_debug_info() is true
   - Expected: header.is_pic() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
header.set_executable(true)
header.set_reloadable(true)
header.set_debug_info(true)
header.set_pic(true)

expect(header.is_executable()).to_equal(true)
expect(header.is_reloadable()).to_equal(true)
expect(header.has_debug_info()).to_equal(true)
expect(header.is_pic()).to_equal(true)
```

</details>

#### stores compression and stub metadata

- var header = SmfHeader new v1 1
- header set compression
- header set stub info
   - Expected: header.get_compression() equals `CompressionType.Zstd`
   - Expected: header.compression_level equals `3`
   - Expected: header.get_stub_size() equals `1024`
   - Expected: header.get_smf_data_offset() equals `1024`
   - Expected: header.has_stub() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var header = SmfHeader.new_v1_1(Platform.Windows, Arch.Aarch64)
header.set_compression(CompressionType.Zstd, 3)
header.set_stub_info(1024, 1024)

expect(header.get_compression()).to_equal(CompressionType.Zstd)
expect(header.compression_level).to_equal(3)
expect(header.get_stub_size()).to_equal(1024)
expect(header.get_smf_data_offset()).to_equal(1024)
expect(header.has_stub()).to_equal(true)
```

</details>

#### serializes to the fixed header size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = SmfHeader.new_v1_1(Platform.Linux, Arch.X86_64)
expect(header.to_bytes().len()).to_equal(SMF_HEADER_SIZE)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
