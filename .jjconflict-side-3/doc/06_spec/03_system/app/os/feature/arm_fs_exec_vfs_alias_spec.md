# ARM FS Exec VFS Alias Spec

> Verifies the ARM FAT32 bridge maps the migrated guest filesystem apps and

<!-- sdn-diagram:id=arm_fs_exec_vfs_alias_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=arm_fs_exec_vfs_alias_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

arm_fs_exec_vfs_alias_spec -> std
arm_fs_exec_vfs_alias_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=arm_fs_exec_vfs_alias_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ARM FS Exec VFS Alias Spec

Verifies the ARM FAT32 bridge maps the migrated guest filesystem apps and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/arm_fs_exec_vfs_alias_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the ARM FAT32 bridge maps the migrated guest filesystem apps and
toolchain manifests to the same canonical disk aliases used by the generic VFS.

## Scenarios

### arm_fs_exec_vfs aliases

#### maps canonical tool app ids onto FAT32 short names

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_fs_exec_disk_alias("/sys/apps/hello_world.smf")).to_equal("/SYS/APPS/HELLOSMF.SMF")
expect(arm_fs_exec_disk_alias("/sys/apps/simple_compiler")).to_equal("/SYS/APPS/SCOMPSMF.SMF")
expect(arm_fs_exec_disk_alias("/sys/apps/simple_interpreter")).to_equal("/SYS/APPS/SINTSMF.SMF")
expect(arm_fs_exec_disk_alias("/sys/apps/simple_loader")).to_equal("/SYS/APPS/SLOADSMF.SMF")
expect(arm_fs_exec_disk_alias("/sys/apps/simple")).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(arm_fs_exec_disk_alias("/sys/apps/simple.smf")).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(arm_fs_exec_disk_alias("/usr/bin/simple")).to_equal("/SYS/APPS/SIMPLSTC.SMF")
expect(arm_fs_exec_disk_alias("/sys/apps/llvm")).to_equal("/SYS/APPS/LLVMSMF.SMF")
expect(arm_fs_exec_disk_alias("/sys/apps/rust")).to_equal("/SYS/APPS/RUSTSMF.SMF")
```

</details>

#### maps toolchain manifests through the ARM SYS directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(arm_fs_exec_disk_alias("/SYS/LLVMMAN.TXT")).to_equal("/SYS/LLVMMAN.TXT")
expect(arm_fs_exec_disk_alias("/SYS/RUSTMAN.TXT")).to_equal("/SYS/RUSTMAN.TXT")
expect(arm_fs_exec_disk_alias("/SYS/TOOLSET.SDN")).to_equal("/SYS/TOOLSET.SDN")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
