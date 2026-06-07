# Smf Driver Manifest Build Specification

> 1. var opts = SmfBuildOptions create

<!-- sdn-diagram:id=smf_driver_manifest_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_driver_manifest_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_driver_manifest_build_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_driver_manifest_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Driver Manifest Build Specification

## Scenarios

### SMF driver manifest build

#### emits a .drv_manifest section when build options carry DRVS bytes

1. var opts = SmfBuildOptions create
   - Expected: section_count equals `2`
   - Expected: smf[section_table + 64] equals `14`
   - Expected: drv_size equals `16`
   - Expected: le_u32(smf, drv_offset) equals `0x44525653`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var opts = SmfBuildOptions.create(Target.x86_64_unknown_linux_gnu())
opts.driver_manifest_bytes = [
    0x53, 0x56, 0x52, 0x44,  # DRVS little endian
    0, 0, 1, 0,              # kind, class, abi_rev
    0, 0, 0, 0,              # vendor
    0, 0, 0, 0               # device_count
]

val smf = generate_smf_with_options([0xC3], opts)
val header = smf.len() - 128
val section_count = le_u32(smf, header + 16)
val section_table = le_u64(smf, header + 20)

expect(section_count).to_equal(2)
expect(find_byte(smf, 14)).to_be_greater_than(0)
expect(smf[section_table + 64]).to_equal(14)

val drv_offset = le_u64(smf, section_table + 64 + 8)
val drv_size = le_u64(smf, section_table + 64 + 16)
expect(drv_size).to_equal(16)
expect(le_u32(smf, drv_offset)).to_equal(0x44525653)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/smf_driver_manifest_build_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF driver manifest build

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
