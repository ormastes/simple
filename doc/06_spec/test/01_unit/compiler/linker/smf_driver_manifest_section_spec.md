# Smf Driver Manifest Section Specification

> <details>

<!-- sdn-diagram:id=smf_driver_manifest_section_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_driver_manifest_section_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_driver_manifest_section_spec -> compiler
smf_driver_manifest_section_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_driver_manifest_section_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Driver Manifest Section Specification

## Scenarios

### SMF driver manifest section

#### reserves .drv_manifest section type and wire value

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SectionType.DrvManifest.name()).to_equal(".drv_manifest")
expect(SectionType.DrvManifest.to_wire_u8()).to_equal(14u8)
```

</details>

#### reserves .launch_meta section type and wire value

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SectionType.LaunchMeta.name()).to_equal(".launch_meta")
expect(SectionType.LaunchMeta.to_wire_u8()).to_equal(15u8)
```

</details>

#### adds DRVS manifest payload as a read-only 8-byte-aligned section

1. var writer = SmfWriter create
   - Expected: idx equals `0`
   - Expected: writer.section_count() equals `1`
   - Expected: section.name equals `.drv_manifest`
   - Expected: section.section_type equals `SectionType.DrvManifest`
   - Expected: section.flags equals `SECTION_FLAG_READ`
   - Expected: section.alignment equals `8`
   - Expected: section.data.len() equals `bytes.len()`
   - Expected: section.data[0] equals `bytes[0] as i64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DriverManifest.for_driver("ahci", "1.0", DriverClass.Block, 0x8086, [0x2922, 0x2829])
val bytes = encode_manifest(manifest)
var writer = SmfWriter.create()
val idx = writer.add_driver_manifest_section(bytes)
expect(idx).to_equal(0)
expect(writer.section_count()).to_equal(1)
val section = writer.sections[0]
expect(section.name).to_equal(".drv_manifest")
expect(section.section_type).to_equal(SectionType.DrvManifest)
expect(section.flags).to_equal(SECTION_FLAG_READ)
expect(section.alignment).to_equal(8)
expect(section.data.len()).to_equal(bytes.len())
expect(section.data[0]).to_equal(bytes[0] as i64)
```

</details>

#### adds launch metadata payload as a read-only 4-byte-aligned section

1. var writer = SmfWriter create
   - Expected: idx equals `0`
   - Expected: writer.section_count() equals `1`
   - Expected: section.name equals `.launch_meta`
   - Expected: section.section_type equals `SectionType.LaunchMeta`
   - Expected: section.flags equals `SECTION_FLAG_READ`
   - Expected: section.alignment equals `4`
   - Expected: section.data.len() equals `bytes.len()`
   - Expected: section.data[0] equals `115`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = "simple_launch_metadata:\n  entry_kind: \"smf\"\n".bytes()
var writer = SmfWriter.create()
val idx = writer.add_launch_metadata_section(bytes)
expect(idx).to_equal(0)
expect(writer.section_count()).to_equal(1)
val section = writer.sections[0]
expect(section.name).to_equal(".launch_meta")
expect(section.section_type).to_equal(SectionType.LaunchMeta)
expect(section.flags).to_equal(SECTION_FLAG_READ)
expect(section.alignment).to_equal(4)
expect(section.data.len()).to_equal(bytes.len())
expect(section.data[0]).to_equal(115)
```

</details>

#### section payload decodes back to the original driver manifest

1. var writer = SmfWriter create

2. writer add driver manifest section

3. payload push
   - Expected: decoded.kind equals `ManifestKind.Driver`
   - Expected: decoded.dclass equals `DriverClass.Block`
   - Expected: decoded.vendor equals `0x1AF4`
   - Expected: decoded.device_ids[0] equals `0x1001`
   - Expected: decoded.name equals `virtio_blk`
   - Expected: decoded.version equals `0.2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = DriverManifest.for_driver("virtio_blk", "0.2", DriverClass.Block, 0x1AF4, [0x1001])
val bytes = encode_manifest(manifest)
var writer = SmfWriter.create()
writer.add_driver_manifest_section(bytes)
var payload: [u8] = []
for b in writer.sections[0].data:
    payload.push(b as u8)
val decoded = decode_manifest(payload, 0).unwrap()
expect(decoded.kind).to_equal(ManifestKind.Driver)
expect(decoded.dclass).to_equal(DriverClass.Block)
expect(decoded.vendor).to_equal(0x1AF4)
expect(decoded.device_ids[0]).to_equal(0x1001)
expect(decoded.name).to_equal("virtio_blk")
expect(decoded.version).to_equal("0.2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_driver_manifest_section_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF driver manifest section

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
