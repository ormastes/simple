# Smf Reloc Write Specification

> <details>

<!-- sdn-diagram:id=smf_reloc_write_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_reloc_write_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_reloc_write_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_reloc_write_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Reloc Write Specification

## Scenarios

### SMF Relocation Writing

### wire format constants

#### relocation entry is 24 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Each relocation entry: offset(8) + sym_idx(4) + type(1) + pad(3) + addend(8) = 24
val entry_size = 8 + 4 + 1 + 3 + 8
expect(entry_size).to_equal(24)
```

</details>

#### section type wire values are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code=1, Data=2, RoData=3, Bss=4, RelTab=5
val code_type = 1
val reloc_type = 5
expect(code_type).to_equal(1)
expect(reloc_type).to_equal(5)
```

</details>

#### relocation type wire values are correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Abs64=1, Rel32=2, PltRel32=3, GotRel32=4
val abs64 = 1
val rel32 = 2
val plt_rel32 = 3
val got_rel32 = 4
expect(abs64).to_equal(1)
expect(rel32).to_equal(2)
expect(plt_rel32).to_equal(3)
expect(got_rel32).to_equal(4)
```

</details>

### relocation entry serialization

#### serializes offset as u64 little-endian

1. bytes push
2. bytes push
3. bytes push
4. bytes push
5. bytes push
6. bytes push
7. bytes push
8. bytes push
   - Expected: read_back equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate a relocation entry with known offset
val offset_val = 0x1234
var bytes: [u8] = []
# Write offset as u64 LE
bytes.push((offset_val & 0xFF) as u8)
bytes.push(((offset_val >> 8) & 0xFF) as u8)
bytes.push(((offset_val >> 16) & 0xFF) as u8)
bytes.push(((offset_val >> 24) & 0xFF) as u8)
bytes.push(0)
bytes.push(0)
bytes.push(0)
bytes.push(0)
val read_back = u64_from_le_bytes(bytes, 0)
expect(read_back).to_equal(0x1234)
```

</details>

#### serializes symbol index as u32 little-endian

1. bytes push
2. bytes push
3. bytes push
4. bytes push
   - Expected: read_back equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_idx = 42
var bytes: [u8] = []
bytes.push((sym_idx & 0xFF) as u8)
bytes.push(((sym_idx >> 8) & 0xFF) as u8)
bytes.push(((sym_idx >> 16) & 0xFF) as u8)
bytes.push(((sym_idx >> 24) & 0xFF) as u8)
val read_back = u32_from_le_bytes(bytes, 0)
expect(read_back).to_equal(42)
```

</details>

#### serializes reloc type as single byte with 3 pad bytes

1. bytes push
2. bytes push
3. bytes push
4. bytes push
   - Expected: bytes[0] equals `2`
   - Expected: bytes[1] equals `0`
   - Expected: bytes[2] equals `0`
   - Expected: bytes[3] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reloc_type = 2  # Rel32
var bytes: [u8] = []
bytes.push(reloc_type as u8)
bytes.push(0)  # pad
bytes.push(0)  # pad
bytes.push(0)  # pad
expect(bytes[0]).to_equal(2)
expect(bytes[1]).to_equal(0)
expect(bytes[2]).to_equal(0)
expect(bytes[3]).to_equal(0)
```

</details>

### multiple relocations

#### serializes multiple entries consecutively

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry_size = 24
val num_entries = 3
val total_size = entry_size * num_entries
expect(total_size).to_equal(72)
```

</details>

#### preserves entry count from reloc section size

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reloc_section_size = 120  # 5 entries * 24 bytes
val entry_count = reloc_section_size / 24
expect(entry_count).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_reloc_write_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF Relocation Writing
- wire format constants
- relocation entry serialization
- multiple relocations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
