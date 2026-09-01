# fs_driver_durability_conformance_spec

> Shared filesystem durability conformance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fs_driver_durability_conformance_spec

Shared filesystem durability conformance.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/fs_driver_durability_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Shared filesystem durability conformance.

Every adapter may advertise DurableSync only when a real durable owner exists.
The current FAT32, DBFS, NVFS, and NVFS-POSIX paths fail closed with Unsupported because
their present flush path has no block-device barrier. No adapter may report a
successful no-op for a volatile/non-durable implementation.

## Scenarios

### FsDriver durability conformance

#### default block-device durability methods fail closed exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- default block-device durability methods fail closed exactly
   - Expected: probe.flush().unwrap_err() equals `block device does not support durable flush`
   - Expected: probe.flush_ordered().unwrap_err() equals `durability owner unavailable: no acknowledged device flush`
   - Expected: probe.fua_ordered().unwrap_err() equals `durability owner unavailable: no acknowledged FUA boundary`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("default block-device durability methods fail closed exactly")
val probe = UnsupportedDurabilityProbe(marker: 0)
expect(probe.flush().unwrap_err()).to_equal("block device does not support durable flush")
expect(probe.flush_ordered().unwrap_err()).to_equal("durability owner unavailable: no acknowledged device flush")
expect(probe.fua_ordered().unwrap_err()).to_equal("durability owner unavailable: no acknowledged FUA boundary")
```

</details>

#### RamFS fails closed because it has no durable backend

- RamFS fails closed because it has no durable backend
   - Expected: mt.fsync(handle).unwrap_err() equals `FsError.Unsupported`
   - Expected: mt.fdatasync(handle).unwrap_err() equals `FsError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("RamFS fails closed because it has no durable backend")
var mt = MountTable.new()
mt.mount("/", DriverInstance.RamFs(driver: RamFsDriver.new()), MountOptions.default())
expect(has_durable(mt)).to_be(false)
val handle = mt.open("/volatile", OpenFlags.create_write()).unwrap()
expect(mt.fsync(handle).unwrap_err()).to_equal(FsError.Unsupported)
expect(mt.fdatasync(handle).unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### FAT32 fails closed until a durable sync implementation is provided

- FAT32 fails closed until a durable sync implementation is provided
   - Expected: mt.fsync(handle).unwrap_err() equals `FsError.Unsupported`
   - Expected: mt.fdatasync(handle).unwrap_err() equals `FsError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("FAT32 fails closed until a durable sync implementation is provided")
var mt = MountTable.new()
mt.mount("/", DriverInstance.Fat32(driver: FsFat32Driver.new_ram_backed()), MountOptions.default())
expect(has_durable(mt)).to_be(false)
val handle = mt.open("/fat-volatile", OpenFlags.create_write()).unwrap()
expect(mt.fsync(handle).unwrap_err()).to_equal(FsError.Unsupported)
expect(mt.fdatasync(handle).unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### DBFS refuses durability until WAL commit reaches a device barrier

- DBFS refuses durability until WAL commit reaches a device barrier
   - Expected: mt.fsync(handle).unwrap_err() equals `FsError.Unsupported`
   - Expected: mt.fdatasync(handle).unwrap_err() equals `FsError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("DBFS refuses durability until WAL commit reaches a device barrier")
var mt = MountTable.new()
mt.mount("/", DriverInstance.DbFs(driver: DbFsDriver.new_hosted()), MountOptions.default())
expect(has_durable(mt)).to_be(false)
val handle = mt.open("/durable", OpenFlags.create_write()).unwrap()
expect(mt.fsync(handle).unwrap_err()).to_equal(FsError.Unsupported)
expect(mt.fdatasync(handle).unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### NVFS refuses durability until its backend exposes Flush or FUA

- NVFS refuses durability until its backend exposes Flush or FUA
   - Expected: mt.fsync(handle).unwrap_err() equals `FsError.Unsupported`
   - Expected: mt.fdatasync(handle).unwrap_err() equals `FsError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS refuses durability until its backend exposes Flush or FUA")
var mt = MountTable.new()
mt.mount("/", DriverInstance.Nvfs(driver: NvfsDriver.new("nvfs")), MountOptions.default())
expect(has_durable(mt)).to_be(false)
val handle = mt.open("/nvfs-durable", OpenFlags.create_write()).unwrap()
expect(mt.fsync(handle).unwrap_err()).to_equal(FsError.Unsupported)
expect(mt.fdatasync(handle).unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### NVFS-POSIX refuses durability until its backend exposes Flush or FUA

- NVFS-POSIX refuses durability until its backend exposes Flush or FUA
   - Expected: mt.fsync(handle).unwrap_err() equals `FsError.Unsupported`
   - Expected: mt.fdatasync(handle).unwrap_err() equals `FsError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("NVFS-POSIX refuses durability until its backend exposes Flush or FUA")
var mt = MountTable.new()
mt.mount("/", DriverInstance.NvfsPosix(driver: NvfsPosixDriver.new("nvfs-posix")), MountOptions.default())
expect(has_durable(mt)).to_be(false)
val handle = mt.open("/nvfs-posix-durable", OpenFlags.create_write()).unwrap()
expect(mt.fsync(handle).unwrap_err()).to_equal(FsError.Unsupported)
expect(mt.fdatasync(handle).unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### capability-gated sync rejects a mount whose request excludes durability

- capability-gated sync rejects a mount whose request excludes durability
   - Expected: mt.fsync(handle).unwrap_err() equals `FsError.Unsupported`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("capability-gated sync rejects a mount whose request excludes durability")
var mt = MountTable.new()
var opts = MountOptions.default()
opts.want_caps = (1 << 23)
mt.mount("/", DriverInstance.DbFs(driver: DbFsDriver.new_hosted()), opts)
expect(has_durable(mt)).to_be(false)
val handle = mt.open("/not-durable", OpenFlags.create_write()).unwrap()
expect(mt.fsync(handle).unwrap_err()).to_equal(FsError.Unsupported)
```

</details>

#### rejects sync through a released global handle before capability dispatch

- rejects sync through a released global handle before capability dispatch
   - Expected: mt.fsync(handle).unwrap_err() equals `FsError.StaleHandle`
   - Expected: mt.fdatasync(handle).unwrap_err() equals `FsError.StaleHandle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects sync through a released global handle before capability dispatch")
var mt = MountTable.new()
mt.mount("/", DriverInstance.RamFs(driver: RamFsDriver.new()), MountOptions.default())
val handle = mt.open("/stale", OpenFlags.create_write()).unwrap()
mt.close(handle).unwrap()
expect(mt.fsync(handle).unwrap_err()).to_equal(FsError.StaleHandle)
expect(mt.fdatasync(handle).unwrap_err()).to_equal(FsError.StaleHandle)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `18552b1109b829778f9b01793305bde50f8a1d812c267af740e582fa08c3c059`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18552b1109b829778f9b01793305bde50f8a1d812c267af740e582fa08c3c059`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18552b1109b829778f9b01793305bde50f8a1d812c267af740e582fa08c3c059`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/storage/fs_driver_durability_conformance_spec.spl
mirror: doc/06_spec/02_integration/storage/fs_driver_durability_conformance_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/fs_driver_durability_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/fs_driver_durability_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/storage/fs_driver_durability_conformance_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'default block-device durability methods fail closed exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/fs_driver_durability_conformance_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'RamFS fails closed because it has no durable backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/storage/fs_driver_durability_conformance_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FAT32 fails closed until a durable sync implementation is provided' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
