# Boot Fs Mount Specification

> <details>

<!-- sdn-diagram:id=boot_fs_mount_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=boot_fs_mount_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

boot_fs_mount_spec -> std
boot_fs_mount_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=boot_fs_mount_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Fs Mount Specification

## Scenarios

### CNvmeBlockAdapterFs — freestanding adapter initial state

#### new adapter is not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = CNvmeBlockAdapterFs(sector_buf_addr: 0, ready: false)
expect(adapter.ready).to_equal(false)
```

</details>

#### new adapter has zero sector_buf_addr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = CNvmeBlockAdapterFs(sector_buf_addr: 0, ready: false)
expect(adapter.sector_buf_addr).to_equal(0)
```

</details>

#### static new produces same zero state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = CNvmeBlockAdapterFs.new()
expect(adapter.ready).to_equal(false)
expect(adapter.sector_buf_addr).to_equal(0)
```

</details>

### FsMountResult — result type structure

#### mounted NVFS result carries correct type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = FsMountResult(mounted: true, fs_type: FsMountType.Nvfs, provider: "c-boot-bridge", pure_simple: false)
expect(r.mounted).to_equal(true)
```

</details>

#### mounted DBFS result carries correct type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = FsMountResult(mounted: true, fs_type: FsMountType.Dbfs, provider: "c-boot-bridge", pure_simple: false)
expect(r.mounted).to_equal(true)
```

</details>

#### unmounted result has None_ type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = FsMountResult(mounted: false, fs_type: FsMountType.None_, provider: "none", pure_simple: false)
expect(r.mounted).to_equal(false)
```

</details>

#### rejects C bridge mount result as pure Simple boot-storage evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c_bridge = FsMountResult(mounted: true, fs_type: FsMountType.Nvfs, provider: "c-boot-bridge", pure_simple: false)
val pure = FsMountResult(mounted: true, fs_type: FsMountType.Nvfs, provider: "simple-driver", pure_simple: true)
expect(boot_fs_mount_provider_is_pure_simple("c-boot-bridge")).to_equal(false)
expect(boot_fs_mount_acceptance_reason(c_bridge)).to_equal("boot-storage-not-pure-simple:c-boot-bridge")
expect(boot_fs_mount_acceptance_reason(pure)).to_equal("ready")
```

</details>

### boot_fs_mount module-level state — initial values

#### fs_mount_done starts false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fs_mount_done()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/kernel/boot_fs_mount_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CNvmeBlockAdapterFs — freestanding adapter initial state
- FsMountResult — result type structure
- boot_fs_mount module-level state — initial values

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
