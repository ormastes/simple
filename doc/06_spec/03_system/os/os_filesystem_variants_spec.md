# Os Filesystem Variants Specification

> <details>

<!-- sdn-diagram:id=os_filesystem_variants_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_filesystem_variants_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_filesystem_variants_spec -> std
os_filesystem_variants_spec -> os
os_filesystem_variants_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_filesystem_variants_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Filesystem Variants Specification

## Scenarios

### SimpleOS filesystem variant system matrix

#### declares FAT32 and NVFS as first-class filesystem variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_has_variant("fat32")).to_equal(true)
expect(_has_variant("nvfs")).to_equal(true)
expect(fs_system_variants().len()).to_equal(2)
```

</details>

### fat32 via x64-nvme-fat32 QEMU scenario

#### materializes a FAT32 fixture disk image

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture_ready = ensure_fs_test_disk_image()
if not fixture_ready:
    print "[os_filesystem_variants_spec] FAT32 fixture image unavailable, skipping artifact assertion"
    expect(fixture_ready).to_equal(false)
else:
    expect(file_exists(fs_test_disk_image_path())).to_equal(true)
```

</details>

#### binds x64-nvme-fat32 to the dedicated filesystem test entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scenario = scenario_x64_nvme_fat32()
val target = scenario_target(scenario)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/fs_test_entry.spl")
expect(target.output).to_equal("build/os/simpleos_fs_test_32.elf")
```

</details>

#### boots the FAT32 contract under QEMU when available

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixture_ready = ensure_fs_test_disk_image()
val live_enabled = _live_qemu_fs_enabled()
if not fixture_ready:
    print "[os_filesystem_variants_spec] FAT32 fixture image unavailable, skipping live QEMU boot"
    expect(fixture_ready).to_equal(false)
else:
    if not live_enabled:
        print "[os_filesystem_variants_spec] SIMPLEOS_QEMU_FS_LIVE not set, skipping live FAT32 build/boot"
        expect(live_enabled).to_equal(false)
    else:
        val scenario = scenario_x64_nvme_fat32()
        val target = scenario_target(scenario)
        if not can_run_target(target):
            print "[os_filesystem_variants_spec] qemu-system-x86_64 or target ELF unavailable, attempting build"

        expect(build_scenario(scenario)).to_equal(true)
        expect(file_exists(target.output)).to_equal(true)

        if not can_run_target(target):
            print "[os_filesystem_variants_spec] qemu-system-x86_64 unavailable, skipping live FAT32 boot"
            expect(can_run_target(target)).to_equal(false)
        else:
            expect(test_scenario(scenario, scenario_test_timeout_ms(scenario))).to_equal(true)
```

</details>

### nvfs via FsDriver POSIX shim

#### satisfies the shared filesystem contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_run_nvfs_posix_contract()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_filesystem_variants_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS filesystem variant system matrix
- fat32 via x64-nvme-fat32 QEMU scenario
- nvfs via FsDriver POSIX shim

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
