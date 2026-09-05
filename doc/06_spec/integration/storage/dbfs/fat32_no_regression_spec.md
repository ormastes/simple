# fat32_no_regression_spec

> FAT32 Hosted Seam Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fat32_no_regression_spec

FAT32 Hosted Seam Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/fat32_no_regression_spec.spl` |
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


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shared FAT32 driver registers without error")
val mt = make_fat32_mounted()
val boot_driver = mt.resolve_driver("/boot").unwrap()
assert_equal(boot_driver.driver_name(), "Fat32Driver")
```

</details>

#### stays on the shared FsFat32Driver surface

- stays on the shared FsFat32Driver surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stays on the shared FsFat32Driver surface")
val source = read_file("test/integration/storage/dbfs/fat32_no_regression_spec.spl")
val legacy_type = "Fat32" + "Driver"
assert_equal(source.contains("use os.services.fat32.fat32"), false)
assert_equal(source.contains(" " + legacy_type + ".new("), false)
assert_equal(source.contains("=" + legacy_type + ".new("), false)
assert_equal(source.contains("(" + legacy_type + ".new("), false)
assert_equal(source.contains("FsFat32Driver.new("), true)
```

</details>

### FAT32 hosted seam — DBFS co-existence

#### FAT32 and DBFS can both be mounted simultaneously

- FAT32 and DBFS can both be mounted simultaneously


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
assert_equal(boot_driver.driver_name(), "Fat32Driver")
assert_equal(data_driver.driver_name(), "DbFsDriver")
```

</details>

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

- Canonical SPipe generation for source `8b56e7667d04162bff2be0ad16b40cb9c7c73a2a5c7d3f6a2c2e52e0d98804f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b56e7667d04162bff2be0ad16b40cb9c7c73a2a5c7d3f6a2c2e52e0d98804f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b56e7667d04162bff2be0ad16b40cb9c7c73a2a5c7d3f6a2c2e52e0d98804f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/fat32_no_regression_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/fat32_no_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/fat32_no_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/fat32_no_regression_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/fat32_no_regression_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shared FAT32 driver registers without error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/fat32_no_regression_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stays on the shared FsFat32Driver surface' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/fat32_no_regression_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FAT32 and DBFS can both be mounted simultaneously' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
