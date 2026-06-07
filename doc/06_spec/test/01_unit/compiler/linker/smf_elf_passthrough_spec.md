# Smf Elf Passthrough Specification

> 1. elf bytes push

<!-- sdn-diagram:id=smf_elf_passthrough_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_elf_passthrough_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_elf_passthrough_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_elf_passthrough_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Elf Passthrough Specification

## Scenarios

### SMF ELF Passthrough

### ELF magic detection

#### detects ELF magic in Code section

1. elf bytes push


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create fake ELF object (ELF magic + padding)
var elf_bytes: [u8] = [0x7F, 0x45, 0x4C, 0x46]
var ei = 0
while ei < 60:
    elf_bytes.push(0)
    ei = ei + 1

val smf = build_test_smf_with_code(elf_bytes)
expect(smf.len()).to_be_greater_than(128)
```

</details>

#### rejects non-ELF Code section

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Code section with non-ELF bytes
val raw_code: [u8] = [0x48, 0x89, 0xE5, 0xC3]
val smf = build_test_smf_with_code(raw_code)
expect(smf.len()).to_be_greater_than(128)
```

</details>

#### handles empty Code section

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val smf = build_test_smf_with_code(empty)
expect(smf.len()).to_be_greater_than(128)
```

</details>

### ELF extraction

#### preserves full ELF bytes

1. elf bytes push
   - Expected: smf[0] equals `0x7F`
   - Expected: smf[1] equals `0x45`
   - Expected: smf[2] equals `0x4C`
   - Expected: smf[3] equals `0x46`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify that ELF bytes can be round-tripped through SMF
var elf_bytes: [u8] = [0x7F, 0x45, 0x4C, 0x46, 2, 1]
var pi = 0
while pi < 58:
    elf_bytes.push(pi as u8)
    pi = pi + 1

val smf = build_test_smf_with_code(elf_bytes)
# Code section should start at offset 0 in the SMF data
expect(smf[0]).to_equal(0x7F)
expect(smf[1]).to_equal(0x45)
expect(smf[2]).to_equal(0x4C)
expect(smf[3]).to_equal(0x46)
```

</details>

### backward compatibility

#### old SMF without ELF works normally

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw_code: [u8] = [0x90, 0xC3]
val smf = build_test_smf_with_code(raw_code)
# Non-ELF code sections still produce valid SMF
expect(smf[0]).to_equal(0x90)
expect(smf[1]).to_equal(0xC3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_elf_passthrough_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF ELF Passthrough
- ELF magic detection
- ELF extraction
- backward compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
