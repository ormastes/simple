# mem_block_device_spec

> MemBlockDevice Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mem_block_device_spec

MemBlockDevice Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/mem_block_device_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

MemBlockDevice Specification

Verifies MemBlockDevice implements BlockDevice with in-memory sector storage:
  new, sector_size, read_sector, write_sector round-trip, bytes, write_to_file

## Scenarios

### MemBlockDevice — construction

#### AC-2: new creates device with correct sector_count

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-2: new creates device with correct sector_count
   - Expected: dev.sector_count() equals `128u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: new creates device with correct sector_count")
# Arrange / Act
val dev = MemBlockDevice.new(128u64, 512u32)
# Assert — sector_count accessor (fails until impl exists)
expect(dev.sector_count()).to_equal(128u64)
```

</details>

#### AC-2: new creates device with correct sector_size

- AC-2: new creates device with correct sector_size
   - Expected: dev.sector_size() equals `512u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: new creates device with correct sector_size")
val dev = MemBlockDevice.new(64u64, 512u32)
expect(dev.sector_size()).to_equal(512u32)
```

</details>

#### AC-2: bytes() length equals sector_count * sector_size

- AC-2: bytes() length equals sector_count * sector_size
   - Expected: b.len() equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: bytes() length equals sector_count * sector_size")
val dev = MemBlockDevice.new(4u64, 512u32)
val b = dev.bytes()
expect(b.len()).to_equal(2048)
```

</details>

### MemBlockDevice — read_sector / write_sector round-trip

#### AC-2: write_sector then read_sector preserves all bytes

- AC-2: write_sector then read_sector preserves all bytes
   - Expected: ok.is_ok() is true
   - Expected: back[0] equals `0xDBu8`
   - Expected: back[511] equals `0xA5u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: write_sector then read_sector preserves all bytes")
val dev = MemBlockDevice.new(8u64, 512u32)
var sector = dev.read_sector(0u64).unwrap()
# Write a known pattern
sector[0] = 0xDBu8
sector[1] = 0xFSu8
sector[511] = 0xA5u8
val ok = dev.write_sector(0u64, sector)
expect(ok.is_ok()).to_equal(true)
val back = dev.read_sector(0u64).unwrap()
expect(back[0]).to_equal(0xDBu8)
expect(back[511]).to_equal(0xA5u8)
```

</details>

#### AC-2: write to sector 3 does not corrupt sector 0

- AC-2: write to sector 3 does not corrupt sector 0
   - Expected: check0[0] equals `0x11u8`
   - Expected: check3[0] equals `0x22u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: write to sector 3 does not corrupt sector 0")
val dev = MemBlockDevice.new(8u64, 512u32)
var s0 = dev.read_sector(0u64).unwrap()
s0[0] = 0x11u8
val _ = dev.write_sector(0u64, s0)
var s3 = dev.read_sector(3u64).unwrap()
s3[0] = 0x22u8
val _ = dev.write_sector(3u64, s3)
val check0 = dev.read_sector(0u64).unwrap()
expect(check0[0]).to_equal(0x11u8)
val check3 = dev.read_sector(3u64).unwrap()
expect(check3[0]).to_equal(0x22u8)
```

</details>

#### AC-2: read_sector out of range returns error

- AC-2: read_sector out of range returns error
   - Expected: result.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: read_sector out of range returns error")
val dev = MemBlockDevice.new(4u64, 512u32)
val result = dev.read_sector(99u64)
expect(result.is_ok()).to_equal(false)
```

</details>

### MemBlockDevice — write_to_file

#### AC-2: write_to_file creates file at the given path

- AC-2: write_to_file creates file at the given path
   - Expected: result.is_ok() is true
   - Expected: rt_file_exists(path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: write_to_file creates file at the given path")
val dev = MemBlockDevice.new(4u64, 512u32)
val path = "/tmp/mem_block_device_spec_test.img"
val result = dev.write_to_file(path)
expect(result.is_ok()).to_equal(true)
expect(rt_file_exists(path)).to_equal(true)
```

</details>

#### AC-2: write_to_file produces file of correct size

- AC-2: write_to_file produces file of correct size
   - Expected: rt_file_size(path) equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("AC-2: write_to_file produces file of correct size")
val dev = MemBlockDevice.new(4u64, 512u32)
val path = "/tmp/mem_block_device_spec_size_test.img"
val _ = dev.write_to_file(path)
expect(rt_file_size(path)).to_equal(2048)
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

- Canonical SPipe generation for source `ea9325429a96a51496df683b3896987109385ba67cfcd2d447c0d1878c2de3f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ea9325429a96a51496df683b3896987109385ba67cfcd2d447c0d1878c2de3f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ea9325429a96a51496df683b3896987109385ba67cfcd2d447c0d1878c2de3f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/integration/storage/dbfs/mem_block_device_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/mem_block_device_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/mem_block_device_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/mem_block_device_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/mem_block_device_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/mem_block_device_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: new creates device with correct sector_count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/mem_block_device_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: new creates device with correct sector_size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/mem_block_device_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-2: bytes() length equals sector_count * sector_size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
