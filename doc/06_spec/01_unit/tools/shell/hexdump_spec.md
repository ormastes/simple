# Hexdump Specification

> <details>

<!-- sdn-diagram:id=hexdump_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hexdump_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hexdump_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hexdump_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hexdump Specification

## Scenarios

### hexdump tool

#### hex formatting

#### converts byte to hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val byte_val = 0xFF
val hi = (byte_val >> 4) & 0xF
val lo = byte_val & 0xF
expect(hi).to_equal(15)
expect(lo).to_equal(15)
```

</details>

#### formats offset as 8 digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offset: u64 = 0
# Offset 0 should produce "00000000"
expect(offset).to_equal(0)
```

</details>

#### ascii display

#### shows printable characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 65  # 'A'
val is_printable = code >= 32 and code < 127
expect(is_printable).to_equal(true)
```

</details>

#### replaces non-printable with dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = 0
val is_printable = code >= 32 and code < 127
expect(is_printable).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/shell/hexdump_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- hexdump tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
