# Byte Cursor Specification

> Tests covering ByteReader/ByteWriter big-endian wire codec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Byte Cursor Specification

## Scenarios

### ByteReader/ByteWriter big-endian wire codec

#### round-trips 0xDEADBEEF through write_u32/read_u32 with exact bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips 0xDEADBEEF through write_u32/read_u32 with exact bytes
   - Expected: bytes.len() equals `4`
   - Expected: bytes[0] equals `0xDEu8`
   - Expected: bytes[1] equals `0xADu8`
   - Expected: bytes[2] equals `0xBEu8`
   - Expected: bytes[3] equals `0xEFu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips 0xDEADBEEF through write_u32/read_u32 with exact bytes")
var w = ByteWriter.new()
w.write_u32(0xDEADBEEFu32)
val bytes = w.to_bytes()
expect(bytes.len()).to_equal(4)
expect(bytes[0]).to_equal(0xDEu8)
expect(bytes[1]).to_equal(0xADu8)
expect(bytes[2]).to_equal(0xBEu8)
expect(bytes[3]).to_equal(0xEFu8)
var r = ByteReader.new(bytes)
match r.read_u32():
    case Ok(v): expect(v).to_equal(0xDEADBEEFu32)
    case Err(_): assert_true(false)
```

</details>

#### read_u8 past end yields a clean Err, never a panic

- read_u8 past end yields a clean Err, never a panic


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("read_u8 past end yields a clean Err, never a panic")
var r = ByteReader.new([])
match r.read_u8():
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_contain("past end")
```

</details>

#### read_bytes past end yields a clean Err

- read_bytes past end yields a clean Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("read_bytes past end yields a clean Err")
val data: [u8] = [1u8, 2u8]
var r = ByteReader.new(data)
match r.read_bytes(5):
    case Ok(_): assert_true(false)
    case Err(msg): expect(msg).to_contain("past end")
```

</details>

#### boundary read at exact remaining length succeeds and drains the cursor

- boundary read at exact remaining length succeeds and drains the cursor
   - Expected: r.remaining() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("boundary read at exact remaining length succeeds and drains the cursor")
val data: [u8] = [0xAAu8, 0xBBu8]
var r = ByteReader.new(data)
match r.read_u16():
    case Ok(v): expect(v).to_equal(0xAABBu16)
    case Err(_): assert_true(false)
expect(r.remaining()).to_equal(0u64)
```

</details>

#### interleaves u8/u16/u24/u32/u48/u64 writes and reads in order

- interleaves u8/u16/u24/u32/u48/u64 writes and reads in order
   - Expected: bytes.len() equals `24`
   - Expected: r.remaining() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("interleaves u8/u16/u24/u32/u48/u64 writes and reads in order")
var w = ByteWriter.new()
w.write_u8(1u8)
w.write_u16(2u16)
w.write_u24(3u32)
w.write_u32(4u32)
w.write_u48(5u64)
w.write_u64(6u64)
val bytes = w.to_bytes()
expect(bytes.len()).to_equal(24)
var r = ByteReader.new(bytes)
match r.read_u8():
    case Ok(v): expect(v).to_equal(1u8)
    case Err(_): assert_true(false)
match r.read_u16():
    case Ok(v): expect(v).to_equal(2u16)
    case Err(_): assert_true(false)
match r.read_u24():
    case Ok(v): expect(v).to_equal(3u32)
    case Err(_): assert_true(false)
match r.read_u32():
    case Ok(v): expect(v).to_equal(4u32)
    case Err(_): assert_true(false)
match r.read_u48():
    case Ok(v): expect(v).to_equal(5u64)
    case Err(_): assert_true(false)
match r.read_u64():
    case Ok(v): expect(v).to_equal(6u64)
    case Err(_): assert_true(false)
expect(r.remaining()).to_equal(0u64)
```

</details>

#### write_bytes/read_bytes round-trips an arbitrary payload

- write_bytes/read_bytes round-trips an arbitrary payload
   - Expected: v[0] equals `0x10u8`
   - Expected: v[1] equals `0x20u8`
   - Expected: v[2] equals `0x30u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("write_bytes/read_bytes round-trips an arbitrary payload")
val payload: [u8] = [0x10u8, 0x20u8, 0x30u8]
var w = ByteWriter.new()
w.write_bytes(payload)
val bytes = w.to_bytes()
var r = ByteReader.new(bytes)
match r.read_bytes(3):
    case Ok(v):
        expect(v[0]).to_equal(0x10u8)
        expect(v[1]).to_equal(0x20u8)
        expect(v[2]).to_equal(0x30u8)
    case Err(_): assert_true(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/net/byte_cursor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ByteReader/ByteWriter big-endian wire codec.
- ByteReader/ByteWriter big-endian wire codec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `0e5ff77c6af3ee9fb6327ca3c7e9c91febc4f4e16046df502cf259ac835ffc31`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e5ff77c6af3ee9fb6327ca3c7e9c91febc4f4e16046df502cf259ac835ffc31`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e5ff77c6af3ee9fb6327ca3c7e9c91febc4f4e16046df502cf259ac835ffc31`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/net/byte_cursor_spec.spl
mirror: doc/06_spec/01_unit/lib/common/net/byte_cursor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/net/byte_cursor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/net/byte_cursor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/net/byte_cursor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/net/byte_cursor_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips 0xDEADBEEF through write_u32/read_u32 with exact bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/net/byte_cursor_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_u8 past end yields a clean Err, never a panic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/net/byte_cursor_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read_bytes past end yields a clean Err' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
