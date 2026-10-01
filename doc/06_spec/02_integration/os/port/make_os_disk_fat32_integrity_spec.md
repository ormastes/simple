# Make Os Disk Fat32 Integrity Specification

> Tests covering SimpleOS direct FAT32 image integrity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Make Os Disk Fat32 Integrity Specification

## Scenarios

### SimpleOS direct FAT32 image integrity

#### uses valid FAT32 geometry and redundant metadata

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses valid FAT32 geometry and redundant metadata
- Inspect dynamic FAT32 geometry and metadata writers


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uses valid FAT32 geometry and redundant metadata")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Inspect dynamic FAT32 geometry and metadata writers")
val source = file_read("scripts/os/make_os_disk.c")
expect(source).to_contain("FAT32_MIN_DATA_CLUSTERS = 65525")
expect(source).to_contain("geometry_for_cluster_size")
expect(source).to_contain("write_fat32_fsinfo")
expect(source).to_contain("memcpy(g_image + (size_t)6 * SECTOR_SIZE, g_image, SECTOR_SIZE)")
expect(source).to_contain("write_fat32_fsinfo((size_t)7 * SECTOR_SIZE)")
expect(source).to_contain("memcpy(g_image + 71, \"SIMPLEOS   \", 11)")
expect(source).to_contain("memcpy(g_image + 82, \"FAT32   \", 8)")
```

</details>

#### owns directory chains and duplicate file chains independently

- owns directory chains and duplicate file chains independently
- Inspect directory allocation, dot entries, and file copies
   - Expected: source does not contain `steam_manifest_cluster`
   - Expected: source does not contain `steam_marker_cluster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("owns directory chains and duplicate file chains independently")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Inspect directory allocation, dot entries, and file copies")
val source = file_read("scripts/os/make_os_disk.c")
expect(source).to_contain("int efi_cluster = alloc_directory()")
expect(source).to_contain("reserve_root_directory()")
expect(source).to_contain("put_dot_entries(usr_bin, &usr_bin_n, usr_bin_cluster, usr_cluster)")
expect(source).to_contain("write_directory(tmp_cluster, tmp, tmp_n)")
expect(source).to_contain("int hello_c_cluster = alloc_clusters(clang_c.data, clang_c.len)")
expect(source).to_contain("int simple_root_cluster = simple_payload.len ? alloc_clusters")
expect(source.contains("steam_manifest_cluster")).to_equal(false)
expect(source.contains("steam_marker_cluster")).to_equal(false)
```

</details>

#### provides reproducible fsck, mtools, manifest, and raw-chain evidence

- provides reproducible fsck, mtools, manifest, and raw-chain evidence
- Inspect the focused integrity checker


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("provides reproducible fsck, mtools, manifest, and raw-chain evidence")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
step("Inspect the focused integrity checker")
val checker = file_read("scripts/check/check-make-os-disk-fat32-integrity.shs")
expect(checker).to_contain("x86_64 fs-exec")
expect(checker).to_contain("x86_64 desktop-fonts")
expect(checker).to_contain("fsck.fat -vn")
expect(checker).to_contain("mdir -i")
expect(checker).to_contain("mtype -i")
expect(checker).to_contain("mshowfat -i")
expect(checker).to_contain("NotoEmoji[wght].ttf")
expect(checker).to_contain("duplicate files unexpectedly share a FAT chain")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/make_os_disk_fat32_integrity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS direct FAT32 image integrity.
- SimpleOS direct FAT32 image integrity

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7645b1c49c193995be3ba265efd96530bfe9248565664c770609768652c8c23f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7645b1c49c193995be3ba265efd96530bfe9248565664c770609768652c8c23f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7645b1c49c193995be3ba265efd96530bfe9248565664c770609768652c8c23f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/os/port/make_os_disk_fat32_integrity_spec.spl
mirror: doc/06_spec/02_integration/os/port/make_os_disk_fat32_integrity_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/02_integration/os/port/make_os_disk_fat32_integrity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/os/port/make_os_disk_fat32_integrity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/os/port/make_os_disk_fat32_integrity_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
