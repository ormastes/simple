# fat32_positioned_vfs_backend_spec

> SOSIX FAT32 positioned backend boundary and failure contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fat32_positioned_vfs_backend_spec

SOSIX FAT32 positioned backend boundary and failure contracts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

SOSIX FAT32 positioned backend boundary and failure contracts.

## Scenarios

### SOSIX FAT32 positioned VFS backend

#### advertises the real cursor-independent primitive implementation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- advertises the real cursor-independent primitive implementation


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advertises the real cursor-independent primitive implementation")
val backend = SosixFat32PositionedVfsBackendV1()
expect(backend.positioned_io_available()).to_be(true)
```

</details>

#### rejects lengths that cannot become a Simple byte-array index

- rejects lengths that cannot become a Simple byte-array index
   - Expected: result.unwrap_err() equals `fat32-positioned-length-overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects lengths that cannot become a Simple byte-array index")
val backend = SosixFat32PositionedVfsBackendV1()
val result = backend.read_at(
    1, 0, SOSIX_FAT32_POSITIONED_MAX_LENGTH_V1 + 1)
expect(result.is_err()).to_be(true)
expect(result.unwrap_err()).to_equal("fat32-positioned-length-overflow")
```

</details>

#### rejects overflowing read and write ranges before kernel dispatch

- rejects overflowing read and write ranges before kernel dispatch
   - Expected: read_result.unwrap_err() equals `fat32-positioned-range-overflow`
   - Expected: write_result.unwrap_err() equals `fat32-positioned-range-overflow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects overflowing read and write ranges before kernel dispatch")
val backend = SosixFat32PositionedVfsBackendV1()
val read_result = backend.read_at(1, 0xffffffffffffffffu64, 1)
val write_result = backend.write_at(1, 0xffffffffffffffffu64, [7])
expect(read_result.unwrap_err()).to_equal("fat32-positioned-range-overflow")
expect(write_result.unwrap_err()).to_equal("fat32-positioned-range-overflow")
```

</details>

#### maps a retired or missing file object to a stable typed reason

- maps a retired or missing file object to a stable typed reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps a retired or missing file object to a stable typed reason")
val backend = SosixFat32PositionedVfsBackendV1()
val read_result = backend.read_at(0, 0, 1)
val write_result = backend.write_at(0, 0, [9])
expect(read_result.unwrap_err()).to_equal(
    "fat32-positioned-file-object-invalid")
expect(write_result.unwrap_err()).to_equal(
    "fat32-positioned-file-object-invalid")
```

</details>

#### maps all admitted FAT32 errno classes without leaking numeric text

- maps all admitted FAT32 errno classes without leaking numeric text


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps all admitted FAT32 errno classes without leaking numeric text")
expect(sosix_fat32_positioned_error_reason_v1(-9)).to_equal(
    "fat32-positioned-file-object-invalid")
expect(sosix_fat32_positioned_error_reason_v1(-38)).to_equal(
    "fat32-positioned-mount-unavailable")
expect(sosix_fat32_positioned_error_reason_v1(-28)).to_equal(
    "fat32-positioned-no-space")
expect(sosix_fat32_positioned_error_reason_v1(-27)).to_equal(
    "fat32-positioned-file-too-large")
expect(sosix_fat32_positioned_error_reason_v1(-16)).to_equal(
    "fat32-positioned-busy")
expect(sosix_fat32_positioned_error_reason_v1(-22)).to_equal(
    "fat32-positioned-invalid-argument")
expect(sosix_fat32_positioned_error_reason_v1(-5)).to_equal(
    "fat32-positioned-io-error")
expect(sosix_fat32_positioned_error_reason_v1(-1234)).to_equal(
    "fat32-positioned-unknown-error")
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b171f26641b26c769ee70df3eb14bc3896ebcd65e38cb3be80f5e2ac194cc247`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b171f26641b26c769ee70df3eb14bc3896ebcd65e38cb3be80f5e2ac194cc247`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b171f26641b26c769ee70df3eb14bc3896ebcd65e38cb3be80f5e2ac194cc247`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advertises the real cursor-independent primitive implementation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects lengths that cannot become a Simple byte-array index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/fat32_positioned_vfs_backend_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects overflowing read and write ranges before kernel dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
