# Fat32 Lfn Parse Specification

> <details>

<!-- sdn-diagram:id=fat32_lfn_parse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_lfn_parse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_lfn_parse_spec -> std
fat32_lfn_parse_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_lfn_parse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fat32 Lfn Parse Specification

## Scenarios

### fat32 LFN parser — single-slot ASCII name

#### decodes one ASCII code unit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = _make_libllvm_so_slot()
val ch = fat32_decode_lfn_code_unit(slot, 1)
expect(ch).to_equal("l")
```

</details>

#### returns empty string for 0x0000 padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = _make_libllvm_so_slot()
# Byte offset 24 is char 11 (0x0000 NUL terminator after 'o')
val ch = fat32_decode_lfn_code_unit(slot, 24)
expect(ch).to_equal("")
```

</details>

#### returns empty string for 0xFFFF padding

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = _make_libllvm_so_slot()
# Byte offset 28 is char 12 (0xFFFF padding)
val ch = fat32_decode_lfn_code_unit(slot, 28)
expect(ch).to_equal("")
```

</details>

#### assembles libLLVM.so from a single slot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val slot = _make_libllvm_so_slot()
val name = fat32_parse_lfn_slot(slot, 0)
expect(name).to_equal("libLLVM.so")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/fat32_lfn_parse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fat32 LFN parser — single-slot ASCII name

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
