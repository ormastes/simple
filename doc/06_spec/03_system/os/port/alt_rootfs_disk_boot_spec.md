# Alt Rootfs Disk Boot Specification

> Tests covering SimpleOS FAT32-carried alternate-rootfs boot smoke, SimpleOS NVFS-marked FAT32 carrier image.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Alt Rootfs Disk Boot Specification

## Scenarios

### SimpleOS FAT32-carried alternate-rootfs boot smoke

#### skips when SIMPLEOS_ALT_ROOTFS_BOOT is not enabled

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- skips when SIMPLEOS_ALT_ROOTFS_BOOT is not enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips when SIMPLEOS_ALT_ROOTFS_BOOT is not enabled")
if not boot_gate():
    return "skip: SIMPLEOS_ALT_ROOTFS_BOOT not set"
return "ok: gate enabled"
```

</details>

### SimpleOS NVFS-marked FAT32 carrier image

#### builds an NVFS-marked image carrying the rootfs marker

- builds an NVFS-marked image carrying the rootfs marker
   - Expected: stage_rootfs_seed() is true
   - Expected: build[2] equals `0`
   - Expected: rt_file_exists(img) is true
   - Expected: marker[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds an NVFS-marked image carrying the rootfs marker")
if not boot_gate():
    return "skip: SIMPLEOS_ALT_ROOTFS_BOOT not set"
reset_backend_root()
expect(stage_rootfs_seed()).to_equal(true)
val build = build_image()
expect(build[2]).to_equal(0)
val img = image_path()
expect(rt_file_exists(img)).to_equal(true)
val marker = rt_process_run("grep", ["-a", "rootfs_backend=nvfs", img])
expect(marker[2]).to_equal(0)
```

</details>

#### boots the NVFS-marked image under QEMU and prints [BOOT]

- boots the NVFS-marked image under QEMU and prints [BOOT]
   - Expected: serial contains `[BOOT]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the NVFS-marked image under QEMU and prints [BOOT]")
if not boot_gate():
    return "skip: SIMPLEOS_ALT_ROOTFS_BOOT not set"
if not qemu_available():
    return "skip: qemu-system-x86_64 not found"
val img = image_path()
if not rt_file_exists(img):
    return "skip: nvfs image not built"
val boot = boot_image()
val serial = boot[0] + boot[1]
expect(serial.contains("[BOOT]")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/port/alt_rootfs_disk_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS FAT32-carried alternate-rootfs boot smoke, SimpleOS NVFS-marked FAT32 carrier image.
- SimpleOS FAT32-carried alternate-rootfs boot smoke
- SimpleOS NVFS-marked FAT32 carrier image

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `55da722215c63b9cda2c29c370022258dbe2065847c400d4429b7ddc39b52a86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `55da722215c63b9cda2c29c370022258dbe2065847c400d4429b7ddc39b52a86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `55da722215c63b9cda2c29c370022258dbe2065847c400d4429b7ddc39b52a86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/os/port/alt_rootfs_disk_boot_spec.spl
mirror: doc/06_spec/03_system/os/port/alt_rootfs_disk_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/port/alt_rootfs_disk_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/port/alt_rootfs_disk_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/port/alt_rootfs_disk_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/port/alt_rootfs_disk_boot_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips when SIMPLEOS_ALT_ROOTFS_BOOT is not enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/port/alt_rootfs_disk_boot_spec.spl:111:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds an NVFS-marked image carrying the rootfs marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/port/alt_rootfs_disk_boot_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots the NVFS-marked image under QEMU and prints [BOOT]' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
