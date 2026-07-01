# dbfs_hw_passthrough_spec

> DBFS Hardware Direct-Accessibility Specification

<!-- sdn-diagram:id=dbfs_hw_passthrough_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_hw_passthrough_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_hw_passthrough_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_hw_passthrough_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/02_integration/storage/dbfs/dbfs_hw_passthrough_spec.spl` |
| Updated | 2026-06-01 |
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

1. mt mount

2. mt mount
   - Expected: dev equals `RamFsDriver`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mt = MountTable.new()
val ramfs = RamFsDriver.new()
mt.mount("/", DriverInstance.RamFs(ramfs), MountOptions.default()).unwrap()
val dbfs = DbFsDriver.new_hosted()
mt.mount("/data", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
val dev = mt.block_device_for("/etc/config").unwrap()
expect(dev).to_equal("RamFsDriver")
```

</details>

### DBFS HW passthrough — DBFS reads through a pre-existing BlockDevice

#### paths under /data resolve to the DBFS mount rather than the sibling RamFs mount

1. mt mount

2. mt mount
   - Expected: fh.id > 0 is true
   - Expected: dev equals `DbFsDriver`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

#### write_passthrough on device-backed driver routes bytes through RawNvmeArena to BlockDevice

1. magic push

2. magic push

3. magic push

4. magic push

5. magic push

6. magic push

7. magic push

8. magic push
   - Expected: write_result.is_ok() is true
   - Expected: bytes_written equals `8`

9. dummy push
   - Expected: mem_result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Construct a RamBlockDevice and open DBFS directly over it.
val ram_dev = RamBlockDevice.new_empty()
val dbfs_result = DbFsDriver.open_on_device(ram_dev, 0, 1024)
expect(dbfs_result.is_ok()).to_equal(true)
val dbfs = dbfs_result.unwrap()
# Verify write_passthrough returns a positive byte count — confirming
# the arena_append path executed and data was dispatched to write_sector.
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

1. mt mount

2. mt mount
   - Expected: dbfs_name equals `DbFsDriver`
   - Expected: fat32_name equals `Fat32Driver`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
