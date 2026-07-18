# ACPI MADT Parser Specification

> <details>

<!-- sdn-diagram:id=madt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=madt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

madt_spec -> std
madt_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=madt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ACPI MADT Parser Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/acpi/madt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### ACPI MADT parser

#### encodes APIC table signature little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ACPI_SIG_APIC).to_equal(0x43495041)
```

</details>

#### extracts enabled local APIC and online-capable x2APIC ids

1. fn r8
2. fn r32
   - Expected: ids.len() equals `2`
   - Expected: ids[0] equals `2u32`
   - Expected: ids[1] equals `0x101u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _make_madt_fixture()
fn r8(off: u64) -> u8: _buf_read8(buf, off)
fn r32(off: u64) -> u32: _buf_read32(buf, off)

val ids = acpi_madt_lapic_ids_raw(r8, r32, 0u64)

expect(ids.len()).to_equal(2)
expect(ids[0]).to_equal(2u32)
expect(ids[1]).to_equal(0x101u32)
```

</details>

#### returns empty ids for undersized MADT

1. fn r8
2. fn r32
   - Expected: ids.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _zero_buf(40u64)
val sized = _put_u32_le(buf, 4u64, 40u32)
fn r8(off: u64) -> u8: _buf_read8(sized, off)
fn r32(off: u64) -> u32: _buf_read32(sized, off)

val ids = acpi_madt_lapic_ids_raw(r8, r32, 0u64)

expect(ids.len()).to_equal(0)
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
