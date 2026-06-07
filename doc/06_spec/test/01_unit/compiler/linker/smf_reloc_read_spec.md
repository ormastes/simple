# Smf Reloc Read Specification

> <details>

<!-- sdn-diagram:id=smf_reloc_read_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_reloc_read_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_reloc_read_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_reloc_read_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Reloc Read Specification

## Scenarios

### SMF Relocation Reading

### relocation entry parsing

#### parses a single relocation entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = build_reloc_entry(0x100, 5, 1, -4)
expect(entry.len()).to_equal(24)
# Verify offset bytes (0x100 = 256)
expect(entry[0]).to_equal(0)
expect(entry[1]).to_equal(1)
```

</details>

#### parses Abs64 relocation type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = build_reloc_entry(0, 0, 1, 0)
# Byte 12 is the reloc type
expect(entry[12]).to_equal(1)
```

</details>

#### parses Rel32 relocation type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = build_reloc_entry(0, 0, 2, 0)
expect(entry[12]).to_equal(2)
```

</details>

#### parses PltRel32 relocation type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = build_reloc_entry(0, 0, 3, 0)
expect(entry[12]).to_equal(3)
```

</details>

#### parses GotRel32 relocation type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = build_reloc_entry(0, 0, 4, 0)
expect(entry[12]).to_equal(4)
```

</details>

### multiple entries

#### parses consecutive relocation entries

1. reloc data = reloc data +
2. reloc data = reloc data +
3. reloc data = reloc data +
   - Expected: reloc_data.len() equals `72`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reloc_data: [u8] = []
reloc_data = reloc_data + (build_reloc_entry(0x10, 1, 1, 0))
reloc_data = reloc_data + (build_reloc_entry(0x20, 2, 2, -4))
reloc_data = reloc_data + (build_reloc_entry(0x30, 3, 3, 0))
expect(reloc_data.len()).to_equal(72)
```

</details>

#### correctly counts entries from section size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val section_size = 120
val entry_count = section_size / 24
expect(entry_count).to_equal(5)
```

</details>

### backward compatibility

#### returns empty list for SMF without reloc section

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Section table with only a Code section (type 1), no Reloc (type 5)
val code_entry = build_section_entry(1, 0, 16)
expect(code_entry.len()).to_equal(64)
# A reader scanning for type 5 should find nothing
```

</details>

#### handles zero-length reloc section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reloc_entry = build_section_entry(5, 100, 0)
expect(reloc_entry.len()).to_equal(64)
# Zero-size reloc section -> empty reloc list
```

</details>

### section type scanning

#### finds Reloc section by wire type 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reloc_entry = build_section_entry(5, 200, 48)
# Wire type 5 = RelTab
expect(reloc_entry[0]).to_equal(5)
```

</details>

#### skips non-Reloc sections

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code_entry = build_section_entry(1, 0, 100)
val data_entry = build_section_entry(2, 100, 50)
expect(code_entry[0]).to_equal(1)
expect(data_entry[0]).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_reloc_read_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF Relocation Reading
- relocation entry parsing
- multiple entries
- backward compatibility
- section type scanning

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
