# smf_reader_memory_spec

> Validates SMF reader memory functionality.

<!-- sdn-diagram:id=smf_reader_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_reader_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_reader_memory_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_reader_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_reader_memory_spec

Validates SMF reader memory functionality.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `src/compiler/70.backend/linker/test/smf_reader_memory_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Basic Tests

    Validates SMF reader memory functionality.

## Scenarios

### Smf Reader Memory

#### rejects data that is too small

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = SmfReaderMemory.from_data([1, 2, 3])
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects invalid magic

- data push
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = [66, 65, 68, 0]
while data.len() < 128:
    data.push(0)

val result = SmfReaderMemory.from_data(data)
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts a minimal valid SMF and parses the header

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reader = SmfReaderMemory.from_data(create_minimal_smf()).unwrap()
val header = reader.get_header()
val (major, minor) = header.version

expect(major).to_equal(1)
expect(minor).to_equal(1)
expect(header.section_count).to_equal(0)
expect(header.symbol_count).to_equal(0)
expect(reader.data_size()).to_equal(128)
expect(reader.exported_symbols().len()).to_equal(0)
```

</details>

#### accepts v1.1 SMF with header trailer at EOF minus 128

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reader = SmfReaderMemory.from_data(create_trailer_smf()).unwrap()
val header = reader.get_header()
val (major, minor) = header.version

expect(major).to_equal(1)
expect(minor).to_equal(1)
expect(header.header_offset).to_equal(5)
expect(header.section_table_offset).to_equal(5)
expect(header.symbol_table_offset).to_equal(5)
expect(reader.data_size()).to_equal(133)
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
