# dbfs_hw_passthrough_spec

> DBFS Hardware Direct-Accessibility Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_hw_passthrough_spec

DBFS Hardware Direct-Accessibility Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Hardware Direct-Accessibility Specification

Verifies the currently implemented mount-table passthrough seam:
  1. non-DBFS paths still resolve to their own mounted driver
  2. DBFS paths resolve to the DBFS mount rather than falling through to siblings
  3. open_on_device wires write_passthrough through to the backing RamBlockDevice
  4. DBFS and Fat32 driver registrations go through the same MountTable path

## Scenarios

### DBFS HW passthrough — non-DBFS driver resolves BlockDevice

#### RamFsDriver mounted alongside DBFS still resolves its own driver tag

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- RamFsDriver mounted alongside DBFS still resolves its own driver tag
   - Expected: dev equals `ramfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RamFsDriver mounted alongside DBFS still resolves its own driver tag")
val mt = MountTable.new()
val ramfs = RamFsDriver.new()
mt.mount("/", DriverInstance.RamFs(ramfs), MountOptions.default()).unwrap()
val dbfs = DbFsDriver.new_hosted()
mt.mount("/data", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
val dev = mt.block_device_for("/etc/config").unwrap()
expect(dev).to_equal("ramfs")
```

</details>

### DBFS HW passthrough — DBFS reads through a pre-existing BlockDevice

#### paths under /data resolve to the DBFS mount rather than the sibling RamFs mount

- paths under /data resolve to the DBFS mount rather than the sibling RamFs mount
   - Expected: fh.id > 0 is true
   - Expected: dev equals `DbFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("paths under /data resolve to the DBFS mount rather than the sibling RamFs mount")
val mt = MountTable.new()
val ramfs = RamFsDriver.new()
mt.mount("/", DriverInstance.RamFs(ramfs), MountOptions.default()).unwrap()
val dbfs = DbFsDriver.new_hosted()
mt.mount("/data", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
val fh = mt.open("/data/hw_test.bin", OpenFlags.create_write()).unwrap()
expect(fh.id > 0).to_equal(true)
val dev = mt.block_device_for("/data/hw_test.bin").unwrap()
expect(dev).to_equal("DbFsDriver")
```

</details>

### DBFS HW passthrough — open_on_device wires through to backing BlockDevice

#### write_passthrough routes bytes through the canonical DBFS device owner

- write_passthrough routes bytes through the canonical DBFS device owner
   - Expected: dbfs_result.is_ok() is true
   - Expected: write_result.is_ok() is true
   - Expected: bytes_written equals `8`
   - Expected: mem_result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("write_passthrough routes bytes through the canonical DBFS device owner")
# Construct a RamBlockDevice and open DBFS directly over it.
val ram_dev = RamBlockDevice.new_empty()
val dbfs_result = DbFsDriver.open_on_device(ram_dev, 0, 1024)
expect(dbfs_result.is_ok()).to_equal(true)
val dbfs = dbfs_result.unwrap()
# Verify write_passthrough returns a positive byte count — confirming
# the owner append path executed and data was dispatched to write_sector.
var magic: [u8] = []
magic.push(222)   # 0xDE
magic.push(173)   # 0xAD
magic.push(190)   # 0xBE
magic.push(239)   # 0xEF
magic.push(68)    # 0x44 'D'
magic.push(66)    # 0x42 'B'
magic.push(70)    # 0x46 'F'
magic.push(83)    # 0x53 'S'
val write_result = dbfs.write_passthrough(magic)
expect(write_result.is_ok()).to_equal(true)
val bytes_written = write_result.unwrap()
expect(bytes_written).to_equal(8)
# Verify in-memory driver returns Unsupported for write_passthrough
# (arena_base == -1 for new_hosted driver).
val in_mem = DbFsDriver.new_hosted()
var dummy: [u8] = []
dummy.push(1)
val mem_result = in_mem.write_passthrough(dummy)
expect(mem_result.is_err()).to_equal(true)
```

</details>

### DBFS HW passthrough — driver-manifest registration parity

#### DBFS and Fat32 variants both register through MountTable and return correct driver names

- DBFS and Fat32 variants both register through MountTable and return correct driver names
   - Expected: dbfs_name equals `DbFsDriver`
   - Expected: fat32_name equals `Fat32Driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DBFS and Fat32 variants both register through MountTable and return correct driver names")
val mt = MountTable.new()
val dbfs = DbFsDriver.new_hosted()
val fat32 = FsFat32Driver.new_ram_backed()
mt.mount("/data", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
mt.mount("/leg", DriverInstance.Fat32(fat32), MountOptions.default()).unwrap()
val dbfs_name = mt.block_device_for("/data/anything").unwrap()
val fat32_name = mt.block_device_for("/leg/anything").unwrap()
expect(dbfs_name).to_equal("DbFsDriver")
expect(fat32_name).to_equal("Fat32Driver")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `2ee98fc46bcdea771a98326c70991788281aa95f86bfb3dc1a74622c23e7814d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ee98fc46bcdea771a98326c70991788281aa95f86bfb3dc1a74622c23e7814d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ee98fc46bcdea771a98326c70991788281aa95f86bfb3dc1a74622c23e7814d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_hw_passthrough_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_hw_passthrough_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_hw_passthrough_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RamFsDriver mounted alongside DBFS still resolves its own driver tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'paths under /data resolve to the DBFS mount rather than the sibling RamFs mount' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_hw_passthrough_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'write_passthrough routes bytes through the canonical DBFS device owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
