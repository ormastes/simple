# Disk Boot Specification

> Tests covering SimpleOS QEMU FAT32 disk-boot smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Disk Boot Specification

## Scenarios

### SimpleOS QEMU FAT32 disk-boot smoke

#### skips when DISK_IMAGE unset

- skips when DISK_IMAGE unset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips when DISK_IMAGE unset")
"""Always returns a skip marker when no image path is configured."""
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
return "ok: DISK_IMAGE is set"
```

</details>

#### disk image exists and is > 10 MB

- disk image exists and is > 10 MB
   - Expected: fs.file_exists(img) is true
   - Expected: size > ten_mb is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disk image exists and is > 10 MB")
"""Skip when DISK_IMAGE is unset; otherwise assert the file exists and exceeds 10 MB."""
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
expect(fs.file_exists(img)).to_equal(true)
val size = fs.file_size(img)
val ten_mb = 10485760
expect(size > ten_mb).to_equal(true)
```

</details>

#### image has FAT32 magic at offset 0x36

- image has FAT32 magic at offset 0x36
   - Expected: code equals `0`
   - Expected: out contains `FAT32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("image has FAT32 magic at offset 0x36")
"""Skip when DISK_IMAGE unset; read first 512 bytes and check FAT32 signature."""
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
val (out, err, code) = process.run("dd", [
    "if={img}",
    "bs=1",
    "skip=54",
    "count=8",
    "status=none",
])
expect(code).to_equal(0)
expect(out.contains("FAT32")).to_equal(true)
```

</details>

#### image carries the expected runtime rootfs backend marker

- image carries the expected runtime rootfs backend marker
   - Expected: code equals `0`
   - Expected: out contains `rootfs_backend={expected}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("image carries the expected runtime rootfs backend marker")
"""Skip when DISK_IMAGE unset; otherwise search the raw image for the rootfs backend marker."""
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
val expected = expected_rootfs_backend()
val (out, err, code) = process.run("grep", [
    "-a",
    "rootfs_backend={expected}",
    img,
])
expect(code).to_equal(0)
expect(out.contains("rootfs_backend={expected}")).to_equal(true)
```

</details>

#### QEMU boot with -drive smoke produces [BOOT] marker within 30s

- QEMU boot with -drive smoke produces [BOOT] marker within 30s
   - Expected: out contains `[BOOT]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU boot with -drive smoke produces [BOOT] marker within 30s")
"""Skip when DISK_IMAGE or qemu binary is missing; otherwise boot and scan stdout."""
val img = disk_image()
if img == "":
    return "skip: DISK_IMAGE not set"
val qemu = qemu_binary()
val qemu_exists = fs.file_exists(qemu)
if qemu_exists == false:
    val (which_out, which_err, which_code) = process.run("which", [qemu])
    if which_code != 0:
        return "skip: qemu binary not found"
val (out, err, code) = process.run(qemu, [
    "-display",
    "none",
    "-serial",
    "stdio",
    "-drive",
    "format=raw,file={img}",
    "-m",
    "128M",
    "-no-reboot",
])
expect(out.contains("[BOOT]")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/disk_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS QEMU FAT32 disk-boot smoke.
- SimpleOS QEMU FAT32 disk-boot smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3a6ee8076408c616e131030812567b4807f81d525cffdec7da607037e02f64e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3a6ee8076408c616e131030812567b4807f81d525cffdec7da607037e02f64e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3a6ee8076408c616e131030812567b4807f81d525cffdec7da607037e02f64e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/port/disk_boot_spec.spl
mirror: doc/06_spec/03_system/os/port/disk_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/port/disk_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/port/disk_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/port/disk_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/port/disk_boot_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips when DISK_IMAGE unset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/port/disk_boot_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disk image exists and is > 10 MB' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/port/disk_boot_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'image has FAT32 magic at offset 0x36' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
