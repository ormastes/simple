# nvfs_image_builder_spec

> NVFS POSIX DBFS-backed Image Builder Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# nvfs_image_builder_spec

NVFS POSIX DBFS-backed Image Builder Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/nvfs/nvfs_image_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

NVFS POSIX DBFS-backed Image Builder Specification

Checks that the compatibility image carries NVFS selection metadata at LBA
0/1, validated DBFS backing metadata at LBA 2/3, and a device-backed seed.

## Scenarios

### NVFS POSIX DBFS-backed image layout

#### rejects images too small for both superblocks and the backing arena

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects images too small for both superblocks and the backing arena
   - Expected: _nvfs_image_mem_device(cfg).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects images too small for both superblocks and the backing arena")
val cfg = NvfsImageConfig(size_sectors: 7u64, seeds: [])
expect(_nvfs_image_mem_device(cfg).is_err()).to_equal(true)
```

</details>

#### formats both NVFS and DBFS replica regions

- formats both NVFS and DBFS replica regions
   - Expected: nvfs_superblock_probe_disk() is true
   - Expected: dbfs_superblock_probe_disk() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("formats both NVFS and DBFS replica regions")
val dev = _nvfs_image_mem_device(_small_nvfs_cfg()).unwrap()
nvfs_superblock_set_device(dev)
dbfs_superblock_set_device(dev)
expect(nvfs_superblock_probe_disk()).to_equal(true)
expect(dbfs_superblock_probe_disk()).to_equal(true)
```

</details>

#### serializes the exact DBFS backing arena count

- serializes the exact DBFS backing arena count
   - Expected: dbfs_superblock_validate(backing) is true
   - Expected: backing.block_count equals `252u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("serializes the exact DBFS backing arena count")
val dev = _nvfs_image_mem_device(_small_nvfs_cfg()).unwrap()
dbfs_superblock_set_device(dev)
val backing = dbfs_superblock_read_from_disk()
expect(dbfs_superblock_validate(backing)).to_equal(true)
expect(backing.block_count).to_equal(252u64)
```

</details>

#### places NVFS and DBFS magic in their assigned sectors

- places NVFS and DBFS magic in their assigned sectors
   - Expected: raw[0] equals `0x53u8`
   - Expected: raw[1] equals `0x46u8`
   - Expected: raw[2] equals `0x56u8`
   - Expected: raw[3] equals `0x4Eu8`
   - Expected: raw[lba2] equals `0x44u8`
   - Expected: raw[lba2 + 1] equals `0x42u8`
   - Expected: raw[lba2 + 2] equals `0x46u8`
   - Expected: raw[lba2 + 3] equals `0x53u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("places NVFS and DBFS magic in their assigned sectors")
val raw = _nvfs_image_mem_device(_small_nvfs_cfg()).unwrap().bytes()
expect(raw[0]).to_equal(0x53u8)
expect(raw[1]).to_equal(0x46u8)
expect(raw[2]).to_equal(0x56u8)
expect(raw[3]).to_equal(0x4Eu8)
val lba2 = 2 * SECTOR_SIZE
expect(raw[lba2]).to_equal(0x44u8)
expect(raw[lba2 + 1]).to_equal(0x42u8)
expect(raw[lba2 + 2]).to_equal(0x46u8)
expect(raw[lba2 + 3]).to_equal(0x53u8)
```

</details>

### NVFS POSIX DBFS-backed image seeds

#### reopens a seeded file through the canonical device-backed NVFS driver

- reopens a seeded file through the canonical device-backed NVFS driver
   - Expected: opened_driver.is_ok() is true
   - Expected: opened_file.is_ok() is true
   - Expected: driver.close_handle(handle).is_ok() is true
   - Expected: content equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reopens a seeded file through the canonical device-backed NVFS driver")
val dev = _nvfs_image_mem_device(_seeded_nvfs_cfg()).unwrap()
val opened_driver = NvfsDriver.new_on_device(
    NVFS_IMAGE_PROVIDER, dev, DBFS_ARENA_BASE_LBA, 252
)
expect(opened_driver.is_ok()).to_equal(true)
val driver = opened_driver.unwrap()
val opened_file = driver.open_path(
    Path(raw: "/etc/seed.txt"), OpenFlags.read_only()
)
expect(opened_file.is_ok()).to_equal(true)
val handle = opened_file.unwrap()
val content = driver.read_handle(handle, 5).unwrap()
expect(driver.close_handle(handle).is_ok()).to_equal(true)
expect(content).to_equal("hello")
```

</details>

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8301d04a220cbb107048b7e2611ac0b534918b29dc4317c12ca0d7f89a0f657`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8301d04a220cbb107048b7e2611ac0b534918b29dc4317c12ca0d7f89a0f657`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8301d04a220cbb107048b7e2611ac0b534918b29dc4317c12ca0d7f89a0f657`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/storage/nvfs/nvfs_image_builder_spec.spl
mirror: doc/06_spec/02_integration/storage/nvfs/nvfs_image_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/nvfs/nvfs_image_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/nvfs/nvfs_image_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/nvfs/nvfs_image_builder_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects images too small for both superblocks and the backing arena' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/nvfs/nvfs_image_builder_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats both NVFS and DBFS replica regions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/nvfs/nvfs_image_builder_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes the exact DBFS backing arena count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
