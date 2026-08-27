# fat32_no_regression_spec

> FAT32 Hosted Seam Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fat32_no_regression_spec

FAT32 Hosted Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/fat32_no_regression_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

FAT32 Hosted Seam Specification

Verifies the currently implemented FAT32 mount-table surface:
  - shared FsFat32Driver can still be mounted alongside other filesystems
  - DBFS resolution does not fall through to the FAT32 sibling
  - this seam no longer imports or instantiates the legacy Fat32Driver

## Scenarios

### FAT32 hosted seam — mount table registration

#### shared FAT32 driver registers without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shared FAT32 driver registers without error
   - Expected: boot_driver.driver_name() equals `Fat32Driver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shared FAT32 driver registers without error")
val mt = make_fat32_mounted()
val boot_driver = mt.resolve_driver("/boot").unwrap()
expect(boot_driver.driver_name()).to_equal("Fat32Driver")
```

</details>

#### keeps each shared FsFat32Driver instance independently mounted

- each shared FsFat32Driver instance mounts independently
   - Expected: table.resolve_driver("/boot/ANY.BIN").unwrap().driver_name() equals `Fat32Driver`
   - Expected: table.resolve_driver("/rescue/ANY.BIN").unwrap().driver_name() equals `Fat32Driver`
   - Expected: table.resolve_driver("/missing/ANY.BIN").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("each shared FsFat32Driver instance mounts independently")
val table = MountTable.new()
val boot = FsFat32Driver.new("Fat32Driver", MockFat32BlockDevice.new())
val rescue = FsFat32Driver.new("Fat32Driver", MockFat32BlockDevice.new())
table.mount("/boot", DriverInstance.Fat32(boot), MountOptions.read_only()).unwrap()
table.mount("/rescue", DriverInstance.Fat32(rescue), MountOptions.read_only()).unwrap()
expect(table.resolve_driver("/boot/ANY.BIN").unwrap().driver_name()).to_equal("Fat32Driver")
expect(table.resolve_driver("/rescue/ANY.BIN").unwrap().driver_name()).to_equal("Fat32Driver")
expect(table.resolve_driver("/missing/ANY.BIN").is_err()).to_equal(true)
```

</details>

#### routes atomic replace lifecycle operations through the shared mount table

- routes atomic replace lifecycle operations through the shared mount table
   - Expected: table.stat("/boot/OLD.BIN").is_err() is true
   - Expected: table.stat("/boot/NEW.BIN").is_ok() is true
   - Expected: table.stat("/boot/NEW.BIN").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes atomic replace lifecycle operations through the shared mount table")
var driver = FsFat32Driver.new_ram_backed_with_file("OLD.BIN", "hello")
driver.mount(MountOptions.default()).unwrap()
var table = MountTable.new()
table.mount("/boot", DriverInstance.Fat32(driver), MountOptions.default()).unwrap()
table.rename("/boot/OLD.BIN", "/boot/NEW.BIN").unwrap()
expect(table.stat("/boot/OLD.BIN").is_err()).to_equal(true)
expect(table.stat("/boot/NEW.BIN").is_ok()).to_equal(true)
val opened = table.open("/boot/NEW.BIN", OpenFlags.read_only()).unwrap()
table.ftruncate(opened, 3).unwrap()
table.close(opened).unwrap()
table.unlink("/boot/NEW.BIN").unwrap()
expect(table.stat("/boot/NEW.BIN").is_err()).to_equal(true)
```

</details>

### FAT32 hosted seam — DBFS co-existence

#### FAT32 and DBFS can both be mounted simultaneously

- FAT32 and DBFS can both be mounted simultaneously
   - Expected: boot_driver.driver_name() equals `Fat32Driver`
   - Expected: data_driver.driver_name() equals `DbFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FAT32 and DBFS can both be mounted simultaneously")
val mt = MountTable.new()
val fat32 = make_fat32_driver()
mt.mount("/boot", DriverInstance.Fat32(fat32), MountOptions.read_only()).unwrap()
val dbfs = DbFsDriver.new_hosted()
mt.mount("/data", DriverInstance.DbFs(dbfs), MountOptions.default()).unwrap()
val boot_driver = mt.resolve_driver("/boot").unwrap()
val data_driver = mt.resolve_driver("/data/file.txt").unwrap()
expect(boot_driver.driver_name()).to_equal("Fat32Driver")
expect(data_driver.driver_name()).to_equal("DbFsDriver")
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

- Canonical SPipe generation for source `328fa35dd04a4aa69f88d37362ad86d42a70486018dad85457d872cf7374981d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `328fa35dd04a4aa69f88d37362ad86d42a70486018dad85457d872cf7374981d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `328fa35dd04a4aa69f88d37362ad86d42a70486018dad85457d872cf7374981d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/storage/dbfs/fat32_no_regression_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/fat32_no_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/fat32_no_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/fat32_no_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/dbfs/fat32_no_regression_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shared FAT32 driver registers without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/fat32_no_regression_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps each shared FsFat32Driver instance independently mounted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/dbfs/fat32_no_regression_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes atomic replace lifecycle operations through the shared mount table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
