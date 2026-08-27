# Pem Binary Roundtrip Class Specification

> Tests covering PEM binary round-trip class — high bytes, PEM binary round-trip class — body is real base64, PEM binary round-trip class — line wrapping.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pem Binary Roundtrip Class Specification

## Scenarios

### PEM binary round-trip class — high bytes

#### guards the fixture: the high-byte input really contains bytes >= 0x80

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards the fixture: the high-byte input really contains bytes >= 0x80
   - Expected: der.len() equals `128u64`
   - Expected: der[0] equals `128u8`
   - Expected: der[127] equals `255u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("guards the fixture: the high-byte input really contains bytes >= 0x80")
# Without this, an implementation that silently dropped the high half
# could still satisfy the round-trip assertions below on an empty body.
val der = _high_bytes()
expect(der.len()).to_equal(128u64)
expect(der[0]).to_equal(128u8)
expect(der[127]).to_equal(255u8)
```

</details>

#### round-trips DER made entirely of bytes >= 0x80

- round-trips DER made entirely of bytes >= 0x80
   - Expected: result.is_ok() is true
   - Expected: _bytes_eq(block.der, der) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips DER made entirely of bytes >= 0x80")
val der = _high_bytes()
val result = pem_decode(pem_encode(_label(), der))
expect(result.is_ok()).to_equal(true)
val block = result.unwrap()
expect(_bytes_eq(block.der, der)).to_equal(true)
```

</details>

#### round-trips all 256 byte values exactly

- round-trips all 256 byte values exactly
   - Expected: result.is_ok() is true
   - Expected: _bytes_eq(block.der, der) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips all 256 byte values exactly")
val der = _all_256_bytes()
val result = pem_decode(pem_encode(_label(), der))
expect(result.is_ok()).to_equal(true)
val block = result.unwrap()
expect(_bytes_eq(block.der, der)).to_equal(true)
```

</details>

#### preserves length for all 256 byte values

- preserves length for all 256 byte values
   - Expected: result.is_ok() is true
   - Expected: block.der.len() equals `256u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves length for all 256 byte values")
val der = _all_256_bytes()
val result = pem_decode(pem_encode(_label(), der))
expect(result.is_ok()).to_equal(true)
val block = result.unwrap()
expect(block.der.len()).to_equal(256u64)
```

</details>

### PEM binary round-trip class — body is real base64

#### encodes the 3-byte input 0xFB 0xFF 0xFE as the RFC 4648 answer +//+

- encodes the 3-byte input 0xFB 0xFF 0xFE as the RFC 4648 answer +//+
   - Expected: s contains `+//+`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("encodes the 3-byte input 0xFB 0xFF 0xFE as the RFC 4648 answer +//+")
# Exercises both high bytes and the two alphabet characters ('+', '/')
# that a hand-rolled table most often gets wrong.
val der: [u8] = [0xfbu8, 0xffu8, 0xfeu8]
val pem = pem_encode(_label(), der)
var s = ""
var i: u64 = 0
while i < pem.len():
    s = s + pem[i].to_i64().chr()
    i = i + 1
expect(s.contains("+//+")).to_equal(true)
```

</details>

#### pads a 1-byte body with two '=' characters

- pads a 1-byte body with two '=' characters
   - Expected: s contains `AA==`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("pads a 1-byte body with two '=' characters")
val der: [u8] = [0x00u8]
val pem = pem_encode(_label(), der)
var s = ""
var i: u64 = 0
while i < pem.len():
    s = s + pem[i].to_i64().chr()
    i = i + 1
expect(s.contains("AA==")).to_equal(true)
```

</details>

### PEM binary round-trip class — line wrapping

#### wraps the base64 body at 64 columns

- wraps the base64 body at 64 columns


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("wraps the base64 body at 64 columns")
# 256 bytes of DER is 344 base64 characters, so a correctly wrapped
# body has more than one line and no line longer than 64.
val pem = pem_encode(_label(), _all_256_bytes())
var s = ""
var i: u64 = 0
while i < pem.len():
    s = s + pem[i].to_i64().chr()
    i = i + 1
var longest: i64 = 0
var cur: i64 = 0
var j: i64 = 0
while j < s.len():
    if s.byte_at(j) == 10u8:
        if cur > longest:
            longest = cur
        cur = 0
    else:
        cur = cur + 1
    j = j + 1
if cur > longest:
    longest = cur
# The BEGIN/END marker lines are longer than the body lines, but both
# are well under 64 for the "CERTIFICATE" label, so the bound holds.
expect(longest).to_be_less_than(65)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/pem_binary_roundtrip_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering PEM binary round-trip class — high bytes, PEM binary round-trip class — body is real base64, PEM binary round-trip class — line wrapping.
- PEM binary round-trip class — high bytes
- PEM binary round-trip class — body is real base64
- PEM binary round-trip class — line wrapping

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

- `REQ-SSPEC-UNIT`
- `REQ-CRYPTO-PEM-BINARY-ROUNDTRIP`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9162e08163538be897ae17fc4dcc34eca297363abcc63e104637d5723eb4e549`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9162e08163538be897ae17fc4dcc34eca297363abcc63e104637d5723eb4e549`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9162e08163538be897ae17fc4dcc34eca297363abcc63e104637d5723eb4e549`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/crypto/pem_binary_roundtrip_class_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/pem_binary_roundtrip_class_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/os/crypto/pem_binary_roundtrip_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/pem_binary_roundtrip_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/pem_binary_roundtrip_class_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/crypto/pem_binary_roundtrip_class_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards the fixture: the high-byte input really contains bytes >= 0x80' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/pem_binary_roundtrip_class_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips DER made entirely of bytes >= 0x80' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/pem_binary_roundtrip_class_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips all 256 byte values exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
