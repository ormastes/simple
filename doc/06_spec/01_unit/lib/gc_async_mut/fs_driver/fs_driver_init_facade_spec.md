# Fs Driver Init Facade Specification

> Tests covering gc_async_mut fs_driver package facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Driver Init Facade Specification

## Scenarios

### gc_async_mut fs_driver package facade

#### re-exports core fs-driver contracts and NVFS helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports core fs-driver contracts and NVFS helpers
   - Expected: Path.root().raw equals `/`
   - Expected: OpenFlags.create_write().is_writable() is true
   - Expected: MountOptions.read_only().read_only is true
   - Expected: FsCapabilitySet.of(Capability.PosixCompat).has(Capability.PosixCompat) is true
   - Expected: errno_of(FsError.NotFound) equals `2`
   - Expected: driver.preferred_io_unit_bytes() equals `512`
   - Expected: arena_append_impl(aid, data, 0) equals `2`
   - Expected: arena_total_bytes_impl(aid) equals `2`
   - Expected: NVFS_MAGIC > 0u32 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports core fs-driver contracts and NVFS helpers")
expect(Path.root().raw).to_equal("/")
expect(OpenFlags.create_write().is_writable()).to_equal(true)
expect(MountOptions.read_only().read_only).to_equal(true)
expect(FsCapabilitySet.of(Capability.PosixCompat).has(Capability.PosixCompat)).to_equal(true)
expect(errno_of(FsError.NotFound)).to_equal(2)
val driver = NvfsDriver.new("gc-async-fs-driver")
expect(driver.preferred_io_unit_bytes()).to_equal(512)
val aid = arena_create_impl(0, 64)
val data: [u8] = [0x66, 0x73]
expect(arena_append_impl(aid, data, 0)).to_equal(2)
expect(arena_total_bytes_impl(aid)).to_equal(2)
expect(NVFS_MAGIC > 0u32).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut fs_driver package facade.
- gc_async_mut fs_driver package facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e565be65227e972c0b596dcc6da2a67f7fa15b3b052163c74f47505382c76172`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e565be65227e972c0b596dcc6da2a67f7fa15b3b052163c74f47505382c76172`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e565be65227e972c0b596dcc6da2a67f7fa15b3b052163c74f47505382c76172`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/fs_driver/fs_driver_init_facade_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports core fs-driver contracts and NVFS helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
