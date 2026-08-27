# Os Filesystem Variants Specification

> Tests covering SimpleOS filesystem variant system matrix, fat32 via x64-nvme-fat32 QEMU scenario, nvfs via FsDriver POSIX shim.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Filesystem Variants Specification

## Scenarios

### SimpleOS filesystem variant system matrix

#### declares FAT32 and NVFS as first-class filesystem variants

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares FAT32 and NVFS as first-class filesystem variants
   - Expected: _has_variant("fat32") is true
   - Expected: _has_variant("nvfs") is true
   - Expected: fs_system_variants().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares FAT32 and NVFS as first-class filesystem variants")
expect(_has_variant("fat32")).to_equal(true)
expect(_has_variant("nvfs")).to_equal(true)
expect(fs_system_variants().len()).to_equal(2)
```

</details>

### fat32 via x64-nvme-fat32 QEMU scenario

#### materializes a FAT32 fixture disk image

- materializes a FAT32 fixture disk image
   - Expected: fixture_ready is false
   - Expected: file_exists(fs_test_disk_image_path()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("materializes a FAT32 fixture disk image")
val fixture_ready = ensure_fs_test_disk_image()
if not fixture_ready:
    print "[os_filesystem_variants_spec] FAT32 fixture image unavailable, skipping artifact assertion"
    expect(fixture_ready).to_equal(false)
else:
    expect(file_exists(fs_test_disk_image_path())).to_equal(true)
```

</details>

#### binds x64-nvme-fat32 to the dedicated filesystem test entry

- binds x64-nvme-fat32 to the dedicated filesystem test entry
   - Expected: target.entry equals `examples/09_embedded/simple_os/arch/x86_64/fs_test_entry.spl`
   - Expected: target.output equals `build/os/simpleos_fs_test_32.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds x64-nvme-fat32 to the dedicated filesystem test entry")
val scenario = scenario_x64_nvme_fat32()
val target = scenario_target(scenario)
expect(target.entry).to_equal("examples/09_embedded/simple_os/arch/x86_64/fs_test_entry.spl")
expect(target.output).to_equal("build/os/simpleos_fs_test_32.elf")
```

</details>

#### boots the FAT32 contract under QEMU when available

- boots the FAT32 contract under QEMU when available
   - Expected: fixture_ready is false
   - Expected: live_enabled is false
   - Expected: build_scenario(scenario) is true
   - Expected: file_exists(target.output) is true
   - Expected: can_run_target(target) is false
   - Expected: test_scenario(scenario, scenario_test_timeout_ms(scenario)) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots the FAT32 contract under QEMU when available")
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

- satisfies the shared filesystem contract
   - Expected: _run_nvfs_posix_contract() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("satisfies the shared filesystem contract")
expect(_run_nvfs_posix_contract()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_filesystem_variants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS filesystem variant system matrix, fat32 via x64-nvme-fat32 QEMU scenario, nvfs via FsDriver POSIX shim.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f6f789069a71d9644f976b4d941158365d128dcc408bcf3fedc4e61cb54d1254`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6f789069a71d9644f976b4d941158365d128dcc408bcf3fedc4e61cb54d1254`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6f789069a71d9644f976b4d941158365d128dcc408bcf3fedc4e61cb54d1254`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/os/os_filesystem_variants_spec.spl
mirror: doc/06_spec/03_system/os/os_filesystem_variants_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_filesystem_variants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_filesystem_variants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_filesystem_variants_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/os_filesystem_variants_spec.spl:178:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares FAT32 and NVFS as first-class filesystem variants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_filesystem_variants_spec.spl:187:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'materializes a FAT32 fixture disk image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_filesystem_variants_spec.spl:197:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds x64-nvme-fat32 to the dedicated filesystem test entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
