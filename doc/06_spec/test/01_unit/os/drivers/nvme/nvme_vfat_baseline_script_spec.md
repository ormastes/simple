# Nvme Vfat Baseline Script Specification

> <details>

<!-- sdn-diagram:id=nvme_vfat_baseline_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_vfat_baseline_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_vfat_baseline_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_vfat_baseline_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Vfat Baseline Script Specification

## Scenarios

### NVMe FAT32 VFAT baseline helper scripts

#### diagnoses VFAT preparation readiness without creating mount artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "/tmp/simple_vfat_script_diagnose_mnt"
val img = "/tmp/simple_vfat_script_diagnose.img"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt + " " + img)
expect(cleanup_code).to_equal(0)

val (stdout, _stderr, code) = _shell(
    "VFAT_MNT=" + mnt + " VFAT_IMG=" + img + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs --diagnose"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt + " && test ! -e " + img)

expect(code).to_equal(0)
expect(stdout).to_contain("vfat_prepare_diagnosis:")
expect(stdout).to_contain("mount: " + mnt)
expect(stdout).to_contain("image: " + img)
expect(stdout).to_contain("mountpoint: false")
expect(stdout).to_contain("reason:")
expect(probe_code).to_equal(0)
```

</details>

#### rejects non-positive FAT32 benchmark run counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_stdout, stderr, code) = _shell("FAT32_4K_RUNS=0 scripts/perf/run-fat32-4k-cfat-baseline.shs")

expect(code).to_equal(1)
expect(stderr).to_contain("FAT32_4K_RUNS must be a positive integer")
```

</details>

#### rejects non-positive VFAT preparation image sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "/tmp/simple_vfat_script_bad_size"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_SIZE_MIB=0 VFAT_MNT=" + mnt + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_SIZE_MIB must be a positive integer")
expect(probe_code).to_equal(0)
```

</details>

#### rejects relative VFAT baseline mount paths before benchmark generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = "build/os/perf/VFAT4K.TXT"
val generated = "build/os/perf/fat32_4k_compare_vfat_mnt.spl"
val cleanup = "mkdir -p build/os/perf && " +
    "printf 'vfat_baseline_evidence: ready\\n' > " + artifact + " && " +
    "printf 'stale generated source\\n' > " + generated
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "REQUIRE_VFAT_BASELINE=1 VFAT_MNT=relative-vfat-mount " +
    "scripts/perf/run-fat32-4k-cfat-baseline.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + generated + " && test ! -e " + artifact)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_MNT must be an absolute path")
expect(probe_code).to_equal(0)
```

</details>

#### rejects filesystem root as a VFAT baseline mount path before benchmark generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = "build/os/perf/VFAT4K.TXT"
val generated = "build/os/perf/fat32_4k_compare_vfat_mnt.spl"
val cleanup = "mkdir -p build/os/perf && " +
    "printf 'vfat_baseline_evidence: ready\\n' > " + artifact + " && " +
    "rm -f " + generated
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell(cleanup)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "REQUIRE_VFAT_BASELINE=1 VFAT_MNT=/ " +
    "scripts/perf/run-fat32-4k-cfat-baseline.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + generated + " && test ! -e " + artifact)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_MNT must not be the filesystem root")
expect(probe_code).to_equal(0)
```

</details>

#### rejects relative VFAT preparation mount paths before directory creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "relative-vfat-prepare-mount"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=" + mnt + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_MNT must be an absolute path")
expect(probe_code).to_equal(0)
```

</details>

#### rejects filesystem root as a VFAT preparation mount path

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val img = "/tmp/simple_vfat_script_root_mnt.img"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -f " + img)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=/ VFAT_IMG=" + img + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs --diagnose"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + img)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_MNT must not be the filesystem root")
expect(probe_code).to_equal(0)
```

</details>

#### rejects filesystem root as a VFAT preparation image path

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "/tmp/simple_vfat_script_root_img_mnt"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=" + mnt + " VFAT_IMG=/ " +
    "scripts/perf/prepare-fat32-4k-vfat.shs --diagnose"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_IMG must not be the filesystem root")
expect(probe_code).to_equal(0)
```

</details>

#### rejects missing VFAT preparation image parent directories before creating artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "/tmp/simple_vfat_script_missing_img_parent_mnt"
val parent = "/tmp/simple_vfat_script_missing_img_parent"
val img = parent + "/backing.img"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt + " " + parent)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=" + mnt + " VFAT_IMG=" + img + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs --diagnose"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt + " && test ! -e " + parent)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_IMG parent directory must exist")
expect(probe_code).to_equal(0)
```

</details>

#### rejects unwritable VFAT preparation image parent directories before creating artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "/tmp/simple_vfat_script_unwritable_img_parent_mnt"
val img = "/proc/simple_vfat_script_unwritable.img"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=" + mnt + " VFAT_IMG=" + img + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs --diagnose"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt + " && test ! -e " + img)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_IMG parent directory must be writable")
expect(probe_code).to_equal(0)
```

</details>

#### rejects relative VFAT preparation image paths before creating artifacts

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "/tmp/simple_vfat_script_relative_img_mnt"
val img = "relative-vfat-prepare.img"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt + " " + img)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=" + mnt + " VFAT_IMG=" + img + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt + " && test ! -e " + img)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_IMG must be an absolute path")
expect(probe_code).to_equal(0)
```

</details>

#### rejects VFAT preparation image paths that alias the mount path

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_vfat_script_img_alias"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + path)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=" + path + " VFAT_IMG=" + path + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + path)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_IMG must differ from VFAT_MNT")
expect(probe_code).to_equal(0)
```

</details>

#### rejects VFAT preparation image paths inside the mount path

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mnt = "/tmp/simple_vfat_script_img_inside_mnt"
val img = mnt + "/backing.img"
val (_cleanup_out, _cleanup_err, cleanup_code) = _shell("rm -rf " + mnt)
expect(cleanup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "VFAT_MNT=" + mnt + " VFAT_IMG=" + img + " " +
    "scripts/perf/prepare-fat32-4k-vfat.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + mnt)

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT_IMG must not be inside VFAT_MNT")
expect(probe_code).to_equal(0)
```

</details>

#### reject required VFAT baseline when seeded files are on a non-VFAT filesystem

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val setup = "rm -rf /tmp/simple_vfat_script_spoof && " +
    "mkdir -p /tmp/simple_vfat_script_spoof && " +
    "dd if=/dev/zero of=/tmp/simple_vfat_script_spoof/simple_fat32_4k_vfat_read.bin bs=4096 count=8 status=none && " +
    "dd if=/dev/zero of=/tmp/simple_vfat_script_spoof/simple_fat32_4k_vfat_write.bin bs=4096 count=8 status=none"
val (_setup_out, _setup_err, setup_code) = _shell(setup)
expect(setup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "FAT32_4K_RUNS=1 REQUIRE_VFAT_BASELINE=1 VFAT_MNT=/tmp/simple_vfat_script_spoof " +
    "scripts/perf/run-fat32-4k-cfat-baseline.shs"
)
val (_cleanup_out, _cleanup_err, _cleanup_code) = _shell("rm -rf /tmp/simple_vfat_script_spoof")

expect(code).to_equal(1)
expect(stderr).to_contain("not vfat/msdos")
expect(stderr).to_contain("vfat_baseline_evidence: not-ready")
expect(stderr).to_contain("vfat_mount: /tmp/simple_vfat_script_spoof")
expect(stderr).to_contain("vfat_fstype:")
expect(stderr).to_contain("vfat_read_bytes:")
expect(stderr).to_contain("vfat_write_bytes:")
```

</details>

#### removes stale VFAT evidence artifact when required baseline is not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val artifact = "build/os/perf/VFAT4K.TXT"
val mnt = "/tmp/simple_vfat_script_stale_evidence"
val setup = "rm -rf " + mnt + " && " +
    "mkdir -p " + mnt + " build/os/perf && " +
    "printf 'vfat_baseline_evidence: ready\\n' > " + artifact + " && " +
    "dd if=/dev/zero of=" + mnt + "/simple_fat32_4k_vfat_read.bin bs=4096 count=8 status=none && " +
    "dd if=/dev/zero of=" + mnt + "/simple_fat32_4k_vfat_write.bin bs=4096 count=8 status=none"
val (_setup_out, _setup_err, setup_code) = _shell(setup)
expect(setup_code).to_equal(0)

val (_stdout, stderr, code) = _shell(
    "FAT32_4K_RUNS=1 REQUIRE_VFAT_BASELINE=1 VFAT_MNT=" + mnt + " " +
    "scripts/perf/run-fat32-4k-cfat-baseline.shs"
)
val (_probe_out, _probe_err, probe_code) = _shell("test ! -e " + artifact)
val (_cleanup_out, _cleanup_err, _cleanup_code) = _shell("rm -rf " + mnt)

expect(code).to_equal(1)
expect(stderr).to_contain("vfat_baseline_evidence: not-ready")
expect(probe_code).to_equal(0)
```

</details>

#### rejects preparing VFAT seeds on an existing non-VFAT mount

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_probe_out, _probe_err, probe_code) = _shell("test -d /dev/shm")
if probe_code != 0:
    return

val (_stdout, stderr, code) = _shell("VFAT_MNT=/dev/shm scripts/perf/prepare-fat32-4k-vfat.shs")

expect(code).to_equal(1)
expect(stderr).to_contain("VFAT baseline mount is not vfat/msdos")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_vfat_baseline_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe FAT32 VFAT baseline helper scripts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
