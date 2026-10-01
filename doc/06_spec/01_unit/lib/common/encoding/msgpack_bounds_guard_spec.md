# Msgpack Bounds Guard Specification

> Tests covering MessagePack decode bounds guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Msgpack Bounds Guard Specification

## Scenarios

### MessagePack decode bounds guards

#### rejects negative decode positions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative decode positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative decode positions")
val r = msgpack_decode_int([0x01], -1)
assert_equal(r[0], -1)
assert_equal(r[1], -1)
```

</details>

#### rejects truncated multi-byte integer payloads

- rejects truncated multi-byte integer payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated multi-byte integer payloads")
val r = msgpack_decode_int([0xCD, 0x01], 0)
assert_equal(r[0], -1)
assert_equal(r[1], 0)
```

</details>

#### rejects truncated 64-bit type integer payloads

- rejects truncated 64-bit type integer payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated 64-bit type integer payloads")
val unsigned = msgpack_decode_type([0xCF, 0x00, 0x00, 0x00, 0x00, 0x00], 0)
val signed = msgpack_decode_type([0xD3, 0x00, 0x00, 0x00, 0x00, 0x00], 0)
assert_equal(unsigned[0], 0xFF)
assert_equal(unsigned[1], -1)
assert_equal(signed[0], 0xFF)
assert_equal(signed[1], -1)
```

</details>

#### rejects uint64 values outside i64 positive range

- rejects uint64 values outside i64 positive range


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects uint64 values outside i64 positive range")
val typed = msgpack_decode_type([0xCF, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], 0)
val decoded = msgpack_decode_int([0xCF, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], 0)
assert_equal(typed[0], 0xFF)
assert_equal(typed[1], -1)
assert_equal(typed[2], 0)
assert_equal(decoded[0], -1)
assert_equal(decoded[1], 0)
```

</details>

#### rejects truncated type headers

- rejects truncated type headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated type headers")
val r = msgpack_decode_type([0xDA, 0x00], 0)
assert_equal(r[0], 0xFF)
assert_equal(r[1], -1)
assert_equal(r[2], 0)
```

</details>

#### rejects truncated 32-bit type headers

- rejects truncated 32-bit type headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated 32-bit type headers")
val str32 = msgpack_decode_type([0xDB, 0x00, 0x00, 0x00], 0)
val bin32 = msgpack_decode_type([0xC6, 0x00, 0x00, 0x00], 0)
val array32 = msgpack_decode_type([0xDD, 0x00, 0x00, 0x00], 0)
val map32 = msgpack_decode_type([0xDF, 0x00, 0x00, 0x00], 0)
assert_equal(str32[0], 0xFF)
assert_equal(bin32[0], 0xFF)
assert_equal(array32[0], 0xFF)
assert_equal(map32[0], 0xFF)
```

</details>

#### rejects truncated binary type headers

- rejects truncated binary type headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated binary type headers")
val bin8 = msgpack_decode_type([0xC4], 0)
val bin16 = msgpack_decode_type([0xC5, 0x00], 0)
assert_equal(bin8[0], 0xFF)
assert_equal(bin8[1], -1)
assert_equal(bin16[0], 0xFF)
assert_equal(bin16[1], -1)
```

</details>

#### rejects truncated collection type headers

- rejects truncated collection type headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated collection type headers")
val array16 = msgpack_decode_type([0xDC, 0x00], 0)
val map16 = msgpack_decode_type([0xDE, 0x00], 0)
assert_equal(array16[0], 0xFF)
assert_equal(array16[1], -1)
assert_equal(map16[0], 0xFF)
assert_equal(map16[1], -1)
```

</details>

#### rejects truncated string payloads

- rejects truncated string payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncated string payloads")
val r = msgpack_decode_str([0xA3, 0x61], 0)
assert_equal(r[0], "")
assert_equal(r[1], 0)
```

</details>

#### keeps valid int and string decodes

- keeps valid int and string decodes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid int and string decodes")
val i = msgpack_decode_int([0x2A], 0)
assert_equal(i[0], 42)
val s = msgpack_decode_str([0xA0], 0)
assert_equal(s[0], "")
```

</details>

#### decodes valid 64-bit type integer payloads

- decodes valid 64-bit type integer payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes valid 64-bit type integer payloads")
val unsigned = msgpack_decode_type([0xCF, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2A], 0)
val signed = msgpack_decode_type([0xD3, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x2B], 0)
assert_equal(unsigned[0], 0xCF)
assert_equal(unsigned[1], 42)
assert_equal(unsigned[2], 9)
assert_equal(signed[0], 0xD3)
assert_equal(signed[1], 43)
assert_equal(signed[2], 9)
```

</details>

#### decodes valid 32-bit type headers

- decodes valid 32-bit type headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes valid 32-bit type headers")
val str32 = msgpack_decode_type([0xDB, 0x00, 0x00, 0x00, 0x02], 0)
val bin32 = msgpack_decode_type([0xC6, 0x00, 0x00, 0x00, 0x03], 0)
val array32 = msgpack_decode_type([0xDD, 0x00, 0x00, 0x00, 0x04], 0)
val map32 = msgpack_decode_type([0xDF, 0x00, 0x00, 0x00, 0x05], 0)
assert_equal(str32[0], 0xDB)
assert_equal(str32[1], 2)
assert_equal(str32[2], 5)
assert_equal(bin32[0], 0xC6)
assert_equal(bin32[1], 3)
assert_equal(array32[0], 0xDD)
assert_equal(array32[1], 4)
assert_equal(map32[0], 0xDF)
assert_equal(map32[1], 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MessagePack decode bounds guards.
- MessagePack decode bounds guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `8e532acb691bb6d11b3adace9f87bb576e2928b1892e563181a66f430234f3c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e532acb691bb6d11b3adace9f87bb576e2928b1892e563181a66f430234f3c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e532acb691bb6d11b3adace9f87bb576e2928b1892e563181a66f430234f3c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative decode positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncated multi-byte integer payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/msgpack_bounds_guard_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncated 64-bit type integer payloads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
