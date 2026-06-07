# Legacy FAT32 Compatibility Specification

> The production FAT implementation is the shared stdlib Fat32Core surfaced

<!-- sdn-diagram:id=fat32_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fat32_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fat32_spec -> std
fat32_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fat32_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Legacy FAT32 Compatibility Specification

The production FAT implementation is the shared stdlib Fat32Core surfaced

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/fat32/fat32_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

The production FAT implementation is the shared stdlib Fat32Core surfaced
through SharedFat32Driver/FsFat32Driver. This spec keeps the legacy constants
and BPB data type stable without instantiating the retired Fat32Driver.

## Scenarios

### Legacy FAT32 BPB compatibility

#### keeps BPB construction fields available for compatibility coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bpb = Fat32Bpb(
    bytes_per_sector: 512,
    sectors_per_cluster: 8,
    reserved_sectors: 32,
    num_fats: 2,
    total_sectors_32: 2097152,
    fat_size_32: 2048,
    root_cluster: 2
)

expect(bpb.bytes_per_sector).to_equal(512)
expect(bpb.sectors_per_cluster).to_equal(8)
expect(bpb.reserved_sectors).to_equal(32)
expect(bpb.num_fats).to_equal(2)
expect(bpb.total_sectors_32).to_equal(2097152)
expect(bpb.fat_size_32).to_equal(2048)
expect(bpb.root_cluster).to_equal(2)
```

</details>

### Legacy FAT32 constants

#### keeps attribute constants aligned with the shared FAT core

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LEGACY_FAT32_ATTR_DIRECTORY).to_equal(FAT32_ATTR_DIRECTORY)
expect(FAT32_ATTR_LFN).to_equal(FAT32_ATTR_LONG_NAME)
expect(FAT32_ATTR_READ_ONLY).to_equal(0x01)
expect(FAT32_ATTR_HIDDEN).to_equal(0x02)
expect(FAT32_ATTR_SYSTEM).to_equal(0x04)
expect(FAT32_ATTR_VOLUME_ID).to_equal(0x08)
expect(FAT32_ATTR_ARCHIVE).to_equal(0x20)
```

</details>

#### keeps special FAT values stable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(FAT32_FREE).to_equal(0x00000000)
expect(FAT32_EOC).to_equal(0x0FFFFFF8)
expect(FAT32_BAD).to_equal(0x0FFFFFF7)
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
