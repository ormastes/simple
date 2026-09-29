# Finished App Traffic Specification

> Tests covering build_finished_bytes wire format, parse_finished_body identity, build → strip-header → parse round-trip, tls13_ct_bytes_equal semantics.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Finished App Traffic Specification

## Scenarios

### build_finished_bytes wire format

#### emits 0x14 type byte and 3-byte length for SHA-256 verify_data (32B)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits 0x14 type byte and 3-byte length for SHA-256 verify_data (32B)
   - Expected: msg.len().to_u64() equals `36u64`
   - Expected: msg[0] equals `0x14u8`
   - Expected: msg[1] equals `0x00u8`
   - Expected: msg[2] equals `0x00u8`
   - Expected: msg[3] equals `0x20u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 0x14 type byte and 3-byte length for SHA-256 verify_data (32B)")
val vd = _vd_pattern(32u64, 0xA0u8)
val msg = build_finished_bytes(vd)
# 1B type + 3B length + 32B body
expect(msg.len().to_u64()).to_equal(36u64)
expect(msg[0]).to_equal(0x14u8)
# 24-bit big-endian length encoding 32 → 0x000020
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x20u8)
```

</details>

#### emits 0x14 type byte and 3-byte length for SHA-384 verify_data (48B)

- emits 0x14 type byte and 3-byte length for SHA-384 verify_data (48B)
   - Expected: msg.len().to_u64() equals `52u64`
   - Expected: msg[0] equals `0x14u8`
   - Expected: msg[1] equals `0x00u8`
   - Expected: msg[2] equals `0x00u8`
   - Expected: msg[3] equals `0x30u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits 0x14 type byte and 3-byte length for SHA-384 verify_data (48B)")
val vd = _vd_pattern(48u64, 0x70u8)
val msg = build_finished_bytes(vd)
# 1B type + 3B length + 48B body
expect(msg.len().to_u64()).to_equal(52u64)
expect(msg[0]).to_equal(0x14u8)
# 24-bit big-endian length encoding 48 → 0x000030
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x30u8)
```

</details>

#### places verify_data immediately after the 4-byte header (32B)

- places verify_data immediately after the 4-byte header (32B)
   - Expected: msg[4] equals `vd[0u64]`
   - Expected: msg[20] equals `vd[16u64]`
   - Expected: msg[35] equals `vd[31u64]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("places verify_data immediately after the 4-byte header (32B)")
val vd = _vd_pattern(32u64, 0xA0u8)
val msg = build_finished_bytes(vd)
# Spot-check first/middle/last verify_data byte through the wire format
expect(msg[4]).to_equal(vd[0u64])
expect(msg[20]).to_equal(vd[16u64])
expect(msg[35]).to_equal(vd[31u64])
```

</details>

### parse_finished_body identity

#### returns body bytes unchanged for SHA-256 width (32B)

- returns body bytes unchanged for SHA-256 width (32B)
   - Expected: parsed.len().to_u64() equals `32u64`
   - Expected: tls13_ct_bytes_equal(parsed, vd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns body bytes unchanged for SHA-256 width (32B)")
val vd = _vd_pattern(32u64, 0x11u8)
val parsed = parse_finished_body(vd)
expect(parsed.len().to_u64()).to_equal(32u64)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

#### returns body bytes unchanged for SHA-384 width (48B)

- returns body bytes unchanged for SHA-384 width (48B)
   - Expected: parsed.len().to_u64() equals `48u64`
   - Expected: tls13_ct_bytes_equal(parsed, vd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns body bytes unchanged for SHA-384 width (48B)")
val vd = _vd_pattern(48u64, 0x55u8)
val parsed = parse_finished_body(vd)
expect(parsed.len().to_u64()).to_equal(48u64)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

### build → strip-header → parse round-trip

#### round-trips a 32-byte SHA-256 verify_data

- round-trips a 32-byte SHA-256 verify_data
   - Expected: tls13_ct_bytes_equal(parsed, vd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a 32-byte SHA-256 verify_data")
val vd = _vd_pattern(32u64, 0xC3u8)
val msg = build_finished_bytes(vd)
val body = _strip_finished_header(msg)
val parsed = parse_finished_body(body)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

#### round-trips a 48-byte SHA-384 verify_data

- round-trips a 48-byte SHA-384 verify_data
   - Expected: tls13_ct_bytes_equal(parsed, vd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips a 48-byte SHA-384 verify_data")
val vd = _vd_pattern(48u64, 0x7Fu8)
val msg = build_finished_bytes(vd)
val body = _strip_finished_header(msg)
val parsed = parse_finished_body(body)
expect(tls13_ct_bytes_equal(parsed, vd)).to_equal(true)
```

</details>

### tls13_ct_bytes_equal semantics

#### returns true for identical 32-byte inputs

- returns true for identical 32-byte inputs
   - Expected: tls13_ct_bytes_equal(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for identical 32-byte inputs")
val a = _vd_pattern(32u64, 0x42u8)
val b = _vd_pattern(32u64, 0x42u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(true)
```

</details>

#### returns true for identical 48-byte inputs

- returns true for identical 48-byte inputs
   - Expected: tls13_ct_bytes_equal(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for identical 48-byte inputs")
val a = _vd_pattern(48u64, 0x99u8)
val b = _vd_pattern(48u64, 0x99u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(true)
```

</details>

#### returns true for two empty buffers

- returns true for two empty buffers
   - Expected: tls13_ct_bytes_equal(empty, empty) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for two empty buffers")
val empty: [u8] = []
expect(tls13_ct_bytes_equal(empty, empty)).to_equal(true)
```

</details>

#### returns false on a single-bit flip at the FIRST byte (32B)

- returns false on a single-bit flip at the FIRST byte (32B)
   - Expected: tls13_ct_bytes_equal(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false on a single-bit flip at the FIRST byte (32B)")
val a = _vd_pattern(32u64, 0x42u8)
val b = _flip_byte(a, 0u64, 0x01u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false on a single-bit flip at the LAST byte (32B)

- returns false on a single-bit flip at the LAST byte (32B)
   - Expected: tls13_ct_bytes_equal(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false on a single-bit flip at the LAST byte (32B)")
val a = _vd_pattern(32u64, 0x42u8)
val b = _flip_byte(a, 31u64, 0x80u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false on a single-bit flip at the FIRST byte (48B)

- returns false on a single-bit flip at the FIRST byte (48B)
   - Expected: tls13_ct_bytes_equal(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false on a single-bit flip at the FIRST byte (48B)")
val a = _vd_pattern(48u64, 0x99u8)
val b = _flip_byte(a, 0u64, 0x01u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false on a single-bit flip at the LAST byte (48B)

- returns false on a single-bit flip at the LAST byte (48B)
   - Expected: tls13_ct_bytes_equal(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false on a single-bit flip at the LAST byte (48B)")
val a = _vd_pattern(48u64, 0x99u8)
val b = _flip_byte(a, 47u64, 0x80u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false when lengths differ (32B vs 48B)

- returns false when lengths differ (32B vs 48B)
   - Expected: tls13_ct_bytes_equal(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when lengths differ (32B vs 48B)")
val a = _vd_pattern(32u64, 0x42u8)
val b = _vd_pattern(48u64, 0x42u8)
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

#### returns false when lengths differ (empty vs 32B)

- returns false when lengths differ (empty vs 32B)
   - Expected: tls13_ct_bytes_equal(empty, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false when lengths differ (empty vs 32B)")
val empty: [u8] = []
val b = _vd_pattern(32u64, 0x42u8)
expect(tls13_ct_bytes_equal(empty, b)).to_equal(false)
```

</details>

#### returns false on a multi-byte difference (every byte XORed)

- returns false on a multi-byte difference (every byte XORed)
   - Expected: tls13_ct_bytes_equal(a, b) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false on a multi-byte difference (every byte XORed)")
val a = _vd_pattern(32u64, 0x42u8)
var b: [u8] = []
var i: u64 = 0u64
while i < a.len().to_u64():
    b.push(a[i] ^ 0x55u8)
    i = i + 1u64
expect(tls13_ct_bytes_equal(a, b)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/finished_app_traffic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering build_finished_bytes wire format, parse_finished_body identity, build → strip-header → parse round-trip, tls13_ct_bytes_equal semantics.
- build_finished_bytes wire format
- parse_finished_body identity
- build → strip-header → parse round-trip
- tls13_ct_bytes_equal semantics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
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

- Canonical SPipe generation for source `f795e3fbd67b17ba8c9b42db250370713a807a3aa40fcc2121b57dea45face89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f795e3fbd67b17ba8c9b42db250370713a807a3aa40fcc2121b57dea45face89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f795e3fbd67b17ba8c9b42db250370713a807a3aa40fcc2121b57dea45face89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/finished_app_traffic_spec.spl
mirror: doc/06_spec/unit/os/tls13/finished_app_traffic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/finished_app_traffic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/finished_app_traffic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/finished_app_traffic_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 0x14 type byte and 3-byte length for SHA-256 verify_data (32B)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/finished_app_traffic_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits 0x14 type byte and 3-byte length for SHA-384 verify_data (48B)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/finished_app_traffic_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'places verify_data immediately after the 4-byte header (32B)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
