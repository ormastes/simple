# Checksum Specification

> Tests covering Crc32, Adler32.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Checksum Specification

## Scenarios

### Crc32

#### CRC32(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- CRC32(\
   - Expected: c.raw() equals `0xCBF43926`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CRC32(\")
var c = Crc32.new()
c.update(ByteSpan.new(check_input()))
expect(c.raw()).to_equal(0xCBF43926)
```

</details>

#### CRC32 of empty input == 0

- CRC32 of empty input == 0
   - Expected: c.raw() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("CRC32 of empty input == 0")
var c = Crc32.new()
c.update(ByteSpan.empty())
expect(c.raw()).to_equal(0)
```

</details>

#### incremental update matches single update

- incremental update matches single update
   - Expected: parts.raw() equals `whole.raw()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("incremental update matches single update")
val data = check_input()
var whole = Crc32.new()
whole.update(ByteSpan.new(data))
var parts = Crc32.new()
parts.update(ByteSpan.of(data, 0, 4))
parts.update(ByteSpan.of(data, 4, 5))
expect(parts.raw()).to_equal(whole.raw())
```

</details>

#### value() returns big-endian byte view of the CRC

- value() returns big-endian byte view of the CRC
   - Expected: be.get(0).to_i64() equals `0xCB`
   - Expected: be.get(1).to_i64() equals `0xF4`
   - Expected: be.get(2).to_i64() equals `0x39`
   - Expected: be.get(3).to_i64() equals `0x26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("value() returns big-endian byte view of the CRC")
var c = Crc32.new()
c.update(ByteSpan.new(check_input()))
val be = c.value().to_span()
expect(be.get(0).to_i64()).to_equal(0xCB)
expect(be.get(1).to_i64()).to_equal(0xF4)
expect(be.get(2).to_i64()).to_equal(0x39)
expect(be.get(3).to_i64()).to_equal(0x26)
```

</details>

### Adler32

#### Adler32(\

- Adler32(\
   - Expected: a.raw() equals `0x091E01DE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Adler32(\")
var a = Adler32.new()
a.update(ByteSpan.new(check_input()))
expect(a.raw()).to_equal(0x091E01DE)
```

</details>

#### Adler32 of empty input == 1

- Adler32 of empty input == 1
   - Expected: a.raw() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("Adler32 of empty input == 1")
var a = Adler32.new()
a.update(ByteSpan.empty())
expect(a.raw()).to_equal(1)
```

</details>

#### incremental update matches single update

- incremental update matches single update
   - Expected: parts.raw() equals `whole.raw()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("incremental update matches single update")
val data = check_input()
var whole = Adler32.new()
whole.update(ByteSpan.new(data))
var parts = Adler32.new()
parts.update(ByteSpan.of(data, 0, 3))
parts.update(ByteSpan.of(data, 3, 6))
expect(parts.raw()).to_equal(whole.raw())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/checksum_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Crc32, Adler32.
- Crc32
- Adler32

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c21727a6f71b16256282f49b1f7ddf89fc65d15e713978ffc4e470e2ed4a805`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c21727a6f71b16256282f49b1f7ddf89fc65d15e713978ffc4e470e2ed4a805`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c21727a6f71b16256282f49b1f7ddf89fc65d15e713978ffc4e470e2ed4a805`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/bytes/checksum_spec.spl
mirror: doc/06_spec/01_unit/lib/common/bytes/checksum_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/bytes/checksum_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/bytes/checksum_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/bytes/checksum_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/bytes/checksum_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CRC32(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bytes/checksum_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CRC32 of empty input == 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/bytes/checksum_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'incremental update matches single update' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
