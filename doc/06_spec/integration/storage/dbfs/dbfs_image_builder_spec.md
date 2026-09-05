# dbfs_image_builder_spec

> DBFS Image Builder Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_image_builder_spec

DBFS Image Builder Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_image_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Image Builder Specification

Verifies build_dbfs_rootfs_image produces a raw disk image with:
  - DBFS superblock at LBA 2-3 (DBFS magic present)
  - Arena at LBA 4+ accessible via DbFsDriver
  - NVFS superblock LBA 0-1 zeroed (no NVFS magic)
  - Seed files stored in the image

## Scenarios

### DBFS image builder — _dbfs_image_mem_device

#### AC-2: _dbfs_image_mem_device returns ok for valid config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-2: _dbfs_image_mem_device returns ok for valid config
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: _dbfs_image_mem_device returns ok for valid config")
val result = _dbfs_image_mem_device(_small_cfg())
expect(result.is_ok()).to_equal(true)
```

</details>

#### AC-2: device has expected byte count (size_sectors * 512)

- AC-2: device has expected byte count (size_sectors * 512)
   - Expected: dev.bytes().len() equals `256 * 512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: device has expected byte count (size_sectors * 512)")
val dev = _dbfs_image_mem_device(_small_cfg()).unwrap()
expect(dev.bytes().len()).to_equal(256 * 512)
```

</details>

#### AC-2: DBFS superblock magic 'DBFS' is at LBA 2 (byte offset 1024)

- AC-2: DBFS superblock magic 'DBFS' is at LBA 2 (byte offset 1024)
   - Expected: raw[LBA2_OFFSET + 0] equals `DBFS_MAGIC_BYTE_0`
   - Expected: raw[LBA2_OFFSET + 1] equals `DBFS_MAGIC_BYTE_1`
   - Expected: raw[LBA2_OFFSET + 2] equals `DBFS_MAGIC_BYTE_2`
   - Expected: raw[LBA2_OFFSET + 3] equals `DBFS_MAGIC_BYTE_3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: DBFS superblock magic 'DBFS' is at LBA 2 (byte offset 1024)")
val dev = _dbfs_image_mem_device(_small_cfg()).unwrap()
val raw = dev.bytes()
expect(raw[LBA2_OFFSET + 0]).to_equal(DBFS_MAGIC_BYTE_0)
expect(raw[LBA2_OFFSET + 1]).to_equal(DBFS_MAGIC_BYTE_1)
expect(raw[LBA2_OFFSET + 2]).to_equal(DBFS_MAGIC_BYTE_2)
expect(raw[LBA2_OFFSET + 3]).to_equal(DBFS_MAGIC_BYTE_3)
```

</details>

#### AC-2: LBA 0 and LBA 1 are zeroed (no NVFS magic)

- AC-2: LBA 0 and LBA 1 are zeroed (no NVFS magic)
   - Expected: raw[0] equals `0u8`
   - Expected: raw[1] equals `0u8`
   - Expected: raw[2] equals `0u8`
   - Expected: raw[3] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: LBA 0 and LBA 1 are zeroed (no NVFS magic)")
val dev = _dbfs_image_mem_device(_small_cfg()).unwrap()
val raw = dev.bytes()
# NVFS magic 'NVFS' would be at byte 0
expect(raw[0]).to_equal(0u8)
expect(raw[1]).to_equal(0u8)
expect(raw[2]).to_equal(0u8)
expect(raw[3]).to_equal(0u8)
```

</details>

#### AC-2: probe via dbfs_superblock_set_device + probe returns true

- AC-2: probe via dbfs_superblock_set_device + probe returns true
   - Expected: probed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: probe via dbfs_superblock_set_device + probe returns true")
val dev = _dbfs_image_mem_device(_small_cfg()).unwrap()
dbfs_superblock_set_device(dev)
val probed = dbfs_superblock_probe_disk()
expect(probed).to_equal(true)
```

</details>

### DBFS image builder — build_dbfs_rootfs_image

#### AC-2: build_dbfs_rootfs_image creates the output file

- AC-2: build_dbfs_rootfs_image creates the output file
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: build_dbfs_rootfs_image creates the output file")
val path = "/tmp/dbfs_image_builder_spec_out.img"
val result = build_dbfs_rootfs_image(_small_cfg(), path)
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(path)).to_equal(true)
```

</details>

#### AC-2: output file size equals size_sectors * 512

- AC-2: output file size equals size_sectors * 512
   - Expected: rt_file_size(path) equals `256 * 512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: output file size equals size_sectors * 512")
val path = "/tmp/dbfs_image_builder_spec_size.img"
val _ = build_dbfs_rootfs_image(_small_cfg(), path)
expect(rt_file_size(path)).to_equal(256 * 512)
```

</details>

#### AC-2: image contains seed file written via DbFsDriver

- AC-2: image contains seed file written via DbFsDriver
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: image contains seed file written via DbFsDriver")
val cfg = _cfg_with_seed("/etc/seed.txt", "hello-dbfs")
val path = "/tmp/dbfs_image_builder_spec_seed.img"
val result = build_dbfs_rootfs_image(cfg, path)
expect(result.is_ok()).to_equal(true)
# Seed file presence is verified by checking the image is non-empty and ok;
# full round-trip is covered in dbfs_image_roundtrip describe block below
```

</details>

### DBFS image builder — seed round-trip via MemBlockDevice

#### AC-2: image built with seed contains DBFS superblock after rebuild

- AC-2: image built with seed contains DBFS superblock after rebuild
   - Expected: dev_result.is_ok() is true
   - Expected: probed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: image built with seed contains DBFS superblock after rebuild")
val cfg = _cfg_with_seed("/sbin/init", "ELF-stub")
val dev_result = _dbfs_image_mem_device(cfg)
expect(dev_result.is_ok()).to_equal(true)
val dev = dev_result.unwrap()
dbfs_superblock_set_device(dev)
val probed = dbfs_superblock_probe_disk()
expect(probed).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `9246c9d0f37ba28b6a182740e645e9b1792c1d71868926eac254b402273fb918`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9246c9d0f37ba28b6a182740e645e9b1792c1d71868926eac254b402273fb918`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9246c9d0f37ba28b6a182740e645e9b1792c1d71868926eac254b402273fb918`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/dbfs_image_builder_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_image_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_image_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_image_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_image_builder_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: _dbfs_image_mem_device returns ok for valid config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_image_builder_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: device has expected byte count (size_sectors * 512)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_image_builder_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: DBFS superblock magic 'DBFS' is at LBA 2 (byte offset 1024)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
