# mount_table_dbfs_dispatch_spec

> MountTable DBFS Dispatch Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mount_table_dbfs_dispatch_spec

MountTable DBFS Dispatch Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

MountTable DBFS Dispatch Specification

Verifies that adding DbFs(driver) to the DriverInstance enum routes
path lookups correctly through MountTable longest-prefix match.

## Scenarios

### MountTable DBFS dispatch — longest-prefix routing

#### path under /data routes to DbFsDriver

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- path under /data routes to DbFsDriver
   - Expected: resolved.driver_name() equals `DbFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("path under /data routes to DbFsDriver")
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/data/foo.txt").unwrap()
expect(resolved.driver_name()).to_equal("DbFsDriver")
```

</details>

#### path under / (not /data) routes to RamFsDriver

- path under / (not /data) routes to RamFsDriver
   - Expected: resolved.driver_name() equals `ramfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("path under / (not /data) routes to RamFsDriver")
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/etc/config").unwrap()
expect(resolved.driver_name()).to_equal("ramfs")
```

</details>

#### exact /data route resolves to DbFsDriver

- exact /data route resolves to DbFsDriver
   - Expected: resolved.driver_name() equals `DbFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exact /data route resolves to DbFsDriver")
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/data").unwrap()
expect(resolved.driver_name()).to_equal("DbFsDriver")
```

</details>

#### nested path /data/a/b/c routes to DbFsDriver

- nested path /data/a/b/c routes to DbFsDriver
   - Expected: resolved.driver_name() equals `DbFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("nested path /data/a/b/c routes to DbFsDriver")
val mt = make_table_with_both()
val resolved = mt.resolve_driver("/data/a/b/c").unwrap()
expect(resolved.driver_name()).to_equal("DbFsDriver")
```

</details>

### MountTable DBFS dispatch — exhaustive match compiles clean

#### DriverInstance.DbFs variant is present in driver_name()

- DriverInstance.DbFs variant is present in driver_name()
   - Expected: name equals `DbFsDriver`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DriverInstance.DbFs variant is present in driver_name()")
val driver = DbFsDriver.new_hosted()
val inst = DriverInstance.DbFs(driver)
# driver_name() must handle DbFs variant — if it panics, the match is not exhaustive.
val name = inst.driver_name()
expect(name).to_equal("DbFsDriver")
```

</details>

### MountTable DBFS dispatch — mount/unmount

#### unmount /data leaves / still resolvable

- unmount /data leaves / still resolvable
   - Expected: resolved.driver_name() equals `ramfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("unmount /data leaves / still resolvable")
val mt = make_table_with_both()
mt.unmount("/data").unwrap()
val resolved = mt.resolve_driver("/etc/hosts").unwrap()
expect(resolved.driver_name()).to_equal("ramfs")
```

</details>

#### resolve after unmount of /data returns error for /data path

- resolve after unmount of /data returns error for /data path
   - Expected: resolved.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("resolve after unmount of /data returns error for /data path")
val mt = make_table_with_both()
mt.unmount("/data").unwrap()
# /data no longer has a dedicated mount; falls back to / (RamFs) if present.
# But if MountTable removes sub-prefix entirely, path still resolves to root.
val resolved = mt.resolve_driver("/data/file")
expect(resolved.is_ok()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `a367631141efc82439da53e14ca39f6391d8e7b3621eb27c75c391480946eb1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a367631141efc82439da53e14ca39f6391d8e7b3621eb27c75c391480946eb1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a367631141efc82439da53e14ca39f6391d8e7b3621eb27c75c391480946eb1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'path under /data routes to DbFsDriver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'path under / (not /data) routes to RamFsDriver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/mount_table_dbfs_dispatch_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exact /data route resolves to DbFsDriver' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
